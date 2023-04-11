#include <curses.h>
#include <readline/history.h>
#include <readline/readline.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <openssl/sha.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <string.h>
#include <getopt.h>
#include <string>
using std::string;
#include <deque>
using std::deque;
#include <pthread.h>
#include <utility>
using std::pair;
#include "dh.h"
#include <gmp.h>
#include <openssl/rsa.h>
#include <openssl/aes.h>
#include <time.h>
#include <openssl/rand.h>
#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/sha.h>
#include <openssl/pem.h>
#include <string>
#include <iostream>


const size_t klen = 128;
unsigned char kA[klen];
//decalre bob and alices public key,private key
mpz_t B;
mpz_t A;
mpz_t a;
mpz_t b;

#define MSG_SIZE 1024
#define AES_BLOCK_SIZE 16

// Implement this function to send encrypted_msg and iv to the other party
void send_encrypted_msg_and_iv(const unsigned char *encrypted_msg, const unsigned char *iv);

// Implement this function to receive encrypted_msg and iv from the other party
int receive_encrypted_msg_and_iv(unsigned char *encrypted_msg, unsigned char *iv);

static pthread_t trecv;     /* wait for incoming messagess and post to queue */
void* recvMsg(void*);       /* for trecv */
static pthread_t tcurses;   /* setup curses and draw messages from queue */
void* cursesthread(void*);  /* for tcurses */
/* tcurses will get a queue full of these and redraw the appropriate windows */
struct redraw_data {
	bool resize;
	string msg;
	string sender;
	WINDOW* win;
};
static deque<redraw_data> mq; /* messages and resizes yet to be drawn */
/* manage access to message queue: */
static pthread_mutex_t qmx = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t qcv = PTHREAD_COND_INITIALIZER;

/* XXX different colors for different senders */

/* record chat history as deque of strings: */
static deque<string> transcript;

#define max(a, b)         \
	({ typeof(a) _a = a;    \
	 typeof(b) _b = b;    \
	 _a > _b ? _a : _b; })

/* network stuff... */

int listensock, sockfd;

[[noreturn]] static void fail_exit(const char *msg);

[[noreturn]] static void error(const char *msg)
{
	perror(msg);
	fail_exit("");
}
void generate_private_key(mpz_t a, const mpz_t p) {
    // Initialize the random number generator state
    gmp_randstate_t rand_state;
    gmp_randinit_default(rand_state);

    // Set the seed value to the current time
    gmp_randseed_ui(rand_state, time(NULL));

    // Create a temporary mpz_t variable to hold p - 2
    mpz_t p_minus_2;
    mpz_init(p_minus_2);
    mpz_sub_ui(p_minus_2, p, 2);

    // Generate a random private key a in the range [1, p - 2]
    mpz_urandomm(a, rand_state, p_minus_2);
    mpz_add_ui(a, a, 1); // Shift the range to [1, p - 1)

    // Clear the temporary variable and random number generator state
    mpz_clear(p_minus_2);
    gmp_randclear(rand_state);
}

int initServerNet(int port)
{
	int reuse = 1;
	struct sockaddr_in serv_addr;
	listensock = socket(AF_INET, SOCK_STREAM, 0);
	setsockopt(listensock, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse));
	/* NOTE: might not need the above if you make sure the client closes first */
	if (listensock < 0)
		error("ERROR opening socket");
	bzero((char *) &serv_addr, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	serv_addr.sin_addr.s_addr = INADDR_ANY;
	serv_addr.sin_port = htons(port);
	if (bind(listensock, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) < 0)
		error("ERROR on binding");
	fprintf(stderr, "listening on port %i...\n",port);
	listen(listensock,1);
	socklen_t clilen;
	struct sockaddr_in  cli_addr;
	sockfd = accept(listensock, (struct sockaddr *) &cli_addr, &clilen);
	if (sockfd < 0)
		error("error on accept");
	close(listensock);
	fprintf(stderr, "connection made, starting session...\n");
	/* at this point, should be able to send/recv on sockfd */
	//! Handshake 
	//! Client -- SYN ---> Server
	size_t SYN;
	if (recv(sockfd, &SYN, sizeof(SYN),0) == -1){
		error("failed to receive SYN");
	}

	//! Server -- SYN+1, ACK ---> Server
	SYN += 1;
	char message[256];
	sprintf(message, "%lu,ACK",SYN);
	if (send(sockfd, message, strlen(message), 0) == -1) {
	    error("failed to send SYN+1 and ACK");
	}
	
	//! Client -- ACK ---> Server
	if (recv(sockfd, message, strlen(message), 0) == -1) {
		error("failed to receive ACK");
	}
	//! Handshake

	// TODO Diffie Hellman
	//server is alice
	// Agree on parameters
// p, g (public)
init("params");

// Generates private key a
// a = random number
mpz_init(a);
generate_private_key(a, p);

// Generates public key in A
// A = g^a (mod p)

mpz_init(A);
mpz_powm(A, g, a, p);

// Sends A to Bob 
size_t pklen = mpz_sizeinbase(A, 2) / 8 + (mpz_sizeinbase(A, 2) % 8 != 0 ? 1 : 0);
unsigned char *Abuf = (unsigned char *)malloc(pklen);
mpz_export(Abuf, NULL, 1, sizeof(Abuf[0]), 0, 0, A);

if (send(sockfd, Abuf, pklen, 0) == -1) {
    error("ERROR sending DH public key A");
}

// Receive B from Bob

//init B to all 0s
mpz_init(B);

size_t Bpklen = pLen; 
// Assuming pLen is the size of the large prime p in bytes

//where B will be recieved 
unsigned char *Bbuf = (unsigned char *)malloc(Bpklen);

//recieve B
if (recv(sockfd, Bbuf, Bpklen, 0) == -1) {
    error("ERROR receiving DH public key");
}
// Convert the received data in Bbuf to an mpz_t variable B we initialized ealier in the global scope
mpz_import(B, Bpklen, 1, sizeof(Bbuf[0]), 0, 0, Bbuf);

//printf("Received DH public key B: %Zd\n", B);

// Free the allocated buffer
free(Bbuf);

dhFinal(a, A, B, kA, klen);

//const char* const_kA = (const char*) kA;
//printf(const_kA);

	return 0;
}


static int initClientNet(char* hostname, int port)
{
	struct sockaddr_in serv_addr;
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	struct hostent *server;
	if (sockfd < 0)
		error("ERROR opening socket");
	server = gethostbyname(hostname);
	if (server == NULL) {
		fprintf(stderr,"ERROR, no such host\n");
		exit(0);
	}
	bzero((char *) &serv_addr, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	memcpy(&serv_addr.sin_addr.s_addr,server->h_addr,server->h_length);
	serv_addr.sin_port = htons(port);
	if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
		error("ERROR connecting");
	/* at this point, should be able to send/recv on sockfd */
	//! Handshake 
	//! Client -- SYN ---> Server
	size_t SYN = rand() % 69420 + 100000;
	if (send(sockfd, &SYN,sizeof(SYN),0) == -1){
		error("failed to send SYN");
	}

	//! Server -- SYN+1, ACK ---> Server
	char buffer[256];
	if (recv(sockfd, buffer, sizeof(buffer), 0) == -1) {
	    error("failed to receive message");
	}
	
	string message(buffer);
	size_t delimiter = message.find(",");
	if (delimiter == string::npos) {
	    error("invalid message format");
	}
	string test_syn = message.substr(0, delimiter);
	string ack = message.substr(delimiter + 1);

	//! Client -- ACK ---> Server
	if (stoi(test_syn) == SYN+1){
		if (send(sockfd, ack.c_str(), ack.size() ,0) == -1){
			error("failed to send ACK");
		}
	}
	else exit(0);
	//! Handshake
//client is bob
	// Agree on parameters (p, g)
init("params");

//generate private key b
mpz_init(b);
generate_private_key(b, p);

// Generates public key B (B = g^b (mod p))
mpz_init(B);
mpz_powm(B, g, b, p);


// Sends B to alice 
size_t pklen = mpz_sizeinbase(B, 2) / 8 + (mpz_sizeinbase(B, 2) % 8 != 0 ? 1 : 0);
unsigned char *Bbuf = (unsigned char *)malloc(pklen);
mpz_export(Bbuf, NULL, 1, sizeof(Bbuf[0]), 0, 0, B);

if (send(sockfd, Bbuf, pklen, 0) == -1) {
    error("ERROR sending DH public key B");
}

//rec A from Alice

//init A to all 0s
mpz_init(A);

size_t Apklen = pLen; // Assuming pLen is the size of the large prime p in bytes

//where A will be recieved 
unsigned char *Abuf = (unsigned char *)malloc(Apklen);

if (recv(sockfd, Abuf, Apklen, 0) == -1) {
    error("ERROR receiving DH public key");
}
// Convert the received data in Abuf to an mpz_t variable A we initialized ealier in the global scope
mpz_import(A, Apklen, 1, sizeof(Abuf[0]), 0, 0, Abuf);

//printf("Received DH public key B: %Zd\n", B);

// Free the allocated buffer
free(Abuf);

dhFinal(b, A, B, kA, klen);



//const char* const_kA = (const char*) kA;


	return 0;
}

static int shutdownNetwork()
{
	shutdown(sockfd,2);
	unsigned char dummy[64];
	ssize_t r;
	do {
		r = recv(sockfd,dummy,64,0);
	} while (r != 0 && r != -1);
	close(sockfd);
	return 0;
}

/* end network stuff. */


[[noreturn]] static void fail_exit(const char *msg)
{
	// Make sure endwin() is only called in visual mode. As a note, calling it
	// twice does not seem to be supported and messed with the cursor position.
	if (!isendwin())
		endwin();
	fprintf(stderr, "%s\n", msg);
	exit(EXIT_FAILURE);
}

// Checks errors for (most) ncurses functions. CHECK(fn, x, y, z) is a checked
// version of fn(x, y, z).
#define CHECK(fn, ...) \
	do \
	if (fn(__VA_ARGS__) == ERR) \
	fail_exit(#fn"("#__VA_ARGS__") failed"); \
	while (false)

static bool should_exit = false;

// Message window
static WINDOW *msg_win;
// Separator line above the command (readline) window
static WINDOW *sep_win;
// Command (readline) window
static WINDOW *cmd_win;

// Input character for readline
static unsigned char input;

static int readline_getc(FILE *dummy)
{
	return input;
}

/* if batch is set, don't draw immediately to real screen (use wnoutrefresh
 * instead of wrefresh) */
static void msg_win_redisplay(bool batch, const string& newmsg="", const string& sender="")
{
	if (batch)
		wnoutrefresh(msg_win);
	else {
		wattron(msg_win,COLOR_PAIR(2));
		wprintw(msg_win,"%s:",sender.c_str());
		wattroff(msg_win,COLOR_PAIR(2));
		wprintw(msg_win," %s\n",newmsg.c_str());
		wrefresh(msg_win);
	}
}


//returns messsage encrypted using shared secret(kA)
unsigned char *aes_encrypt(unsigned char key[32], char *message) {
    unsigned char iv[16];
    for (size_t i = 0; i < 16; i++) iv[i] = i;

    unsigned char *ct = (unsigned char *) malloc(512 * sizeof(unsigned char));
    memset(ct, 0, 512);

    size_t len = strlen(message);

    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    if (1 != EVP_EncryptInit_ex(ctx, EVP_aes_256_ctr(), NULL, key, iv))
        ERR_print_errors_fp(stderr);

    int nWritten;
    if (1 != EVP_EncryptUpdate(ctx, ct, &nWritten, (unsigned char *) message, len))
        ERR_print_errors_fp(stderr);

    int nFinal;
    if (1 != EVP_EncryptFinal_ex(ctx, ct + nWritten, &nFinal))
        ERR_print_errors_fp(stderr);

    nWritten += nFinal;
    ct[nWritten] = '\0';

    EVP_CIPHER_CTX_free(ctx);
    return ct;
}

static void msg_typed(char *line) {
    // Declare a string variable to store the message
    string mymsg;

    if (!line) {
        // Ctrl-D pressed on an empty line
        should_exit = true;
        /* XXX send a "goodbye" message so the other end doesn't
         * have to wait for a timeout on recv()? */
    } else {
        if (*line) {
            // Add the line to the readline history
            add_history(line);

            // Store the line (message) in the mymsg variable
            mymsg = string(line);

            // Append the message to the transcript vector with the prefix "me: "
            transcript.push_back("me: " + mymsg);

            // Declare a variable to store the number of bytes sent
            ssize_t nbytes;
			unsigned char *encrypted_line = aes_encrypt(kA,line);

			size_t kAlen = 128;
            // Send the message (line) over the socket
            // Returns the number of bytes sent or -1 if an error occurs
            if ((nbytes = send(sockfd, encrypted_line, kAlen, 0)) == -1)
                error("send failed");
        }

        // Lock the mutex to ensure thread-safe access to the message queue
        pthread_mutex_lock(&qmx);

        // Add the message to the message queue
        mq.push_back({false, mymsg, "me", msg_win});

        // Signal the condition variable to notify the waiting thread
        pthread_cond_signal(&qcv);

        // Unlock the mutex
        pthread_mutex_unlock(&qmx);
    }
}

/* if batch is set, don't draw immediately to real screen (use wnoutrefresh
 * instead of wrefresh) */
static void cmd_win_redisplay(bool batch)
{
	int prompt_width = strnlen(rl_display_prompt, 128);
	int cursor_col = prompt_width + strnlen(rl_line_buffer,rl_point);

	werase(cmd_win);
	mvwprintw(cmd_win, 0, 0, "%s%s", rl_display_prompt, rl_line_buffer);
	/* XXX deal with a longer message than the terminal window can show */
	if (cursor_col >= COLS) {
		// Hide the cursor if it lies outside the window. Otherwise it'll
		// appear on the very right.
		curs_set(0);
	} else {
		wmove(cmd_win,0,cursor_col);
		curs_set(1);
	}
	if (batch)
		wnoutrefresh(cmd_win);
	else
		wrefresh(cmd_win);
}

static void readline_redisplay(void)
{
	pthread_mutex_lock(&qmx);
	mq.push_back({false,"","",cmd_win});
	pthread_cond_signal(&qcv);
	pthread_mutex_unlock(&qmx);
}

static void resize(void)
{
	if (LINES >= 3) {
		wresize(msg_win,LINES-2,COLS);
		wresize(sep_win,1,COLS);
		wresize(cmd_win,1,COLS);
		/* now move bottom two to last lines: */
		mvwin(sep_win,LINES-2,0);
		mvwin(cmd_win,LINES-1,0);
	}

	/* Batch refreshes and commit them with doupdate() */
	msg_win_redisplay(true);
	wnoutrefresh(sep_win);
	cmd_win_redisplay(true);
	doupdate();
}

static void init_ncurses(void)
{
	if (!initscr())
		fail_exit("Failed to initialize ncurses");

	if (has_colors()) {
		CHECK(start_color);
		CHECK(use_default_colors);
	}
	CHECK(cbreak);
	CHECK(noecho);
	CHECK(nonl);
	CHECK(intrflush, NULL, FALSE);

	curs_set(1);

	if (LINES >= 3) {
		msg_win = newwin(LINES - 2, COLS, 0, 0);
		sep_win = newwin(1, COLS, LINES - 2, 0);
		cmd_win = newwin(1, COLS, LINES - 1, 0);
	} else {
		// Degenerate case. Give the windows the minimum workable size to
		// prevent errors from e.g. wmove().
		msg_win = newwin(1, COLS, 0, 0);
		sep_win = newwin(1, COLS, 0, 0);
		cmd_win = newwin(1, COLS, 0, 0);
	}
	if (!msg_win || !sep_win || !cmd_win)
		fail_exit("Failed to allocate windows");

	scrollok(msg_win,true);

	if (has_colors()) {
		// Use white-on-blue cells for the separator window...
		CHECK(init_pair, 1, COLOR_WHITE, COLOR_BLUE);
		CHECK(wbkgd, sep_win, COLOR_PAIR(1));
		/* NOTE: -1 is the default background color, which for me does
		 * not appear to be any of the normal colors curses defines. */
		CHECK(init_pair, 2, COLOR_MAGENTA, -1);
	}
	else {
		wbkgd(sep_win,A_STANDOUT); /* c.f. man curs_attr */
	}
	wrefresh(sep_win);
}

static void deinit_ncurses(void)
{
	delwin(msg_win);
	delwin(sep_win);
	delwin(cmd_win);
	endwin();
}

static void init_readline(void)
{
	// Let ncurses do all terminal and signal handling
	rl_catch_signals = 0;
	rl_catch_sigwinch = 0;
	rl_deprep_term_function = NULL;
	rl_prep_term_function = NULL;

	// Prevent readline from setting the LINES and COLUMNS environment
	// variables, which override dynamic size adjustments in ncurses. When
	// using the alternate readline interface (as we do here), LINES and
	// COLUMNS are not updated if the terminal is resized between two calls to
	// rl_callback_read_char() (which is almost always the case).
	rl_change_environment = 0;

	// Handle input by manually feeding characters to readline
	rl_getc_function = readline_getc;
	rl_redisplay_function = readline_redisplay;

	rl_callback_handler_install("> ", msg_typed);
}

static void deinit_readline(void)
{
	rl_callback_handler_remove();
}

static const char* usage =
"Usage: %s [OPTIONS]...\n"
"Secure chat for CSc380.\n\n"
"   -c, --connect HOST  Attempt a connection to HOST.\n"
"   -l, --listen        Listen for new connections.\n"
"   -p, --port    PORT  Listen or connect on PORT (defaults to 1337).\n"
"   -h, --help          show this message and exit.\n";

int main(int argc, char *argv[])
{
	// define long options
	static struct option long_opts[] = {
		{"connect",  required_argument, 0, 'c'},
		{"listen",   no_argument,       0, 'l'},
		{"port",     required_argument, 0, 'p'},
		{"help",     no_argument,       0, 'h'},
		{0,0,0,0}
	};
	// process options:
	char c;
	int opt_index = 0;
	int port = 1337;
	char hostname[HOST_NAME_MAX+1] = "localhost";
	hostname[HOST_NAME_MAX] = 0;
	bool isclient = true;

	while ((c = getopt_long(argc, argv, "c:lp:h", long_opts, &opt_index)) != -1) {
		switch (c) {
			case 'c':
				if (strnlen(optarg,HOST_NAME_MAX))
					strncpy(hostname,optarg,HOST_NAME_MAX);
				break;
			case 'l':
				isclient = false;
				break;
			case 'p':
				port = atoi(optarg);
				break;
			case 'h':
				printf(usage,argv[0]);
				return 0;
			case '?':
				printf(usage,argv[0]);
				return 1;
		}
	}
	if (isclient) {
		initClientNet(hostname,port);
	} else {
		initServerNet(port);
	}

	/* NOTE: these don't work if called from cursesthread */
	init_ncurses();
	init_readline();
	/* start curses thread */
	if (pthread_create(&tcurses,0,cursesthread,0)) {
		fprintf(stderr, "Failed to create curses thread.\n");
	}
	/* start receiver thread: */
	if (pthread_create(&trecv,0,recvMsg,0)) {
		fprintf(stderr, "Failed to create update thread.\n");
	}

	/* put this in the queue to signal need for resize: */
	redraw_data rd = {false,"","",NULL};
	do {
		int c = wgetch(cmd_win);
		switch (c) {
			case KEY_RESIZE:
				pthread_mutex_lock(&qmx);
				mq.push_back(rd);
				pthread_cond_signal(&qcv);
				pthread_mutex_unlock(&qmx);
				break;
				// Ctrl-L -- redraw screen
			// case '\f':
			// 	// Makes the next refresh repaint the screen from scratch
			// 	/* XXX this needs to be done in the curses thread as well. */
			// 	clearok(curscr,true);
			// 	resize();
			// 	break;
			default:
				input = c;
				rl_callback_read_char();
		}
	} while (!should_exit);

	shutdownNetwork();
	deinit_ncurses();
	deinit_readline();
	return 0;
}

/* Let's have one thread responsible for all things curses.  It should
 * 1. Initialize the library
 * 2. Wait for messages (we'll need a mutex-protected queue)
 * 3. Restore terminal / end curses mode? */

/* We'll need yet another thread to listen for incoming messages and
 * post them to the queue. */

void* cursesthread(void* pData)
{
	/* NOTE: these calls only worked from the main thread... */
	// init_ncurses();
	// init_readline();
	while (true) {
		pthread_mutex_lock(&qmx);
		while (mq.empty()) {
			pthread_cond_wait(&qcv,&qmx);
			/* NOTE: pthread_cond_wait will release the mutex and block, then
			 * reaquire it before returning.  Given that only one thread (this
			 * one) consumes elements of the queue, we probably don't have to
			 * check in a loop like this, but in general this is the recommended
			 * way to do it.  See the man page for details. */
		}
		/* at this point, we have control of the queue, which is not empty,
		 * so write all the messages and then let go of the mutex. */
		while (!mq.empty()) {
			redraw_data m = mq.front();
			mq.pop_front();
			if (m.win == cmd_win) {
				cmd_win_redisplay(m.resize);
			} else if (m.resize) {
				resize();
			} else {
				msg_win_redisplay(false,m.msg,m.sender);
				/* Redraw input window to "focus" it (otherwise the cursor
				 * will appear in the transcript which is confusing). */
				cmd_win_redisplay(false);
			}
		}
		pthread_mutex_unlock(&qmx);
	}
	return 0;
}

void aes_decrypt(unsigned char key[128], unsigned char *ciphertext, int ciphertext_len) {
    unsigned char iv[16];
    for (size_t i = 0; i < 16; i++) iv[i] = i;

    unsigned char pt[512];
    memset(pt, 0, 512);

    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    if (1 != EVP_DecryptInit_ex(ctx, EVP_aes_256_ctr(), NULL, key, iv))
        ERR_print_errors_fp(stderr);

    int nWritten;
    if (1 != EVP_DecryptUpdate(ctx, pt, &nWritten, ciphertext, ciphertext_len))
        ERR_print_errors_fp(stderr);

    int nFinal;
    if (1 != EVP_DecryptFinal_ex(ctx, pt + nWritten, &nFinal))
        ERR_print_errors_fp(stderr);

    nWritten += nFinal;
    printf("decrypted %i bytes:\n%s\n", nWritten, pt);

    EVP_CIPHER_CTX_free(ctx);
}

void* recvMsg(void*)
{
	size_t maxlen = 256;
	char msg[maxlen+1];
	ssize_t nbytes;
	while (1) {
		if ((nbytes = recv(sockfd,msg,maxlen,0)) == -1)
			error("recv failed");
		msg[nbytes] = 0; /* make sure it is null-terminated */
		if (nbytes == 0) {
			/* signal to the main loop that we should quit: */
			should_exit = true;
			return 0;
		}
		
		aes_decrypt(kA, (unsigned char*) msg, 32);

		pthread_mutex_lock(&qmx);
		mq.push_back({false,msg,"Mr Thread",msg_win});
		pthread_cond_signal(&qcv);
		pthread_mutex_unlock(&qmx);
	}
	return 0;
}

static deque<redraw_data> mq; /* messages and resizes yet to be drawn */
/* manage access to message queue: */
static pthread_mutex_t qmx = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t qcv = PTHREAD_COND_INITIALIZER;

/* XXX different colors for different senders */

/* record chat history as deque of strings: */
static deque<string> transcript;

#define max(a, b)         \
	({ typeof(a) _a = a;    \
	 typeof(b) _b = b;    \
	 _a > _b ? _a : _b; })

/* network stuff... */

int listensock, sockfd;

[[noreturn]] static void fail_exit(const char *msg);

[[noreturn]] static void error(const char *msg)
{
	perror(msg);
	fail_exit("");
}

int initServerNet(int port)
{
	int reuse = 1;
	struct sockaddr_in serv_addr;
	listensock = socket(AF_INET, SOCK_STREAM, 0);
	setsockopt(listensock, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse));
	/* NOTE: might not need the above if you make sure the client closes first */
	if (listensock < 0)
		error("ERROR opening socket");
	bzero((char *) &serv_addr, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	serv_addr.sin_addr.s_addr = INADDR_ANY;
	serv_addr.sin_port = htons(port);
	if (bind(listensock, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) < 0)
		error("ERROR on binding");
	fprintf(stderr, "listening on port %i...\n",port);
	listen(listensock,1);
	socklen_t clilen;
	struct sockaddr_in  cli_addr;
	sockfd = accept(listensock, (struct sockaddr *) &cli_addr, &clilen);
	if (sockfd < 0)
		error("error on accept");
	close(listensock);
	fprintf(stderr, "connection made, starting session...\n");
	/* at this point, should be able to send/recv on sockfd */
	//! Handshake 
	//! Client -- SYN ---> Server
	size_t SYN;
	if (recv(sockfd, &SYN, sizeof(SYN),0) == -1){
		error("failed to receive SYN");
	}

	//! Server -- SYN+1, ACK ---> Server
	SYN += 1;
	char message[256];
	sprintf(message, "%lu,ACK",SYN);
	if (send(sockfd, message, strlen(message), 0) == -1) {
	    error("failed to send SYN+1 and ACK");
	}
	
	//! Client -- ACK ---> Server
	if (recv(sockfd, message, strlen(message), 0) == -1) {
		error("failed to receive ACK");
	}
	//! Handshake

	// TODO Diffie Hellman
	// mpz_t B;
	// mpz_init(B);
	// size_t Bpklen = mpz_size(B);
	// if (recv(sockfd, B, Bpklen, 0) == -1) {
	//     error("ERROR receiving DH public key");
	// }
	// printf("Received DH public key B: %Zd\n", B);

	return 0;
}


static int initClientNet(char* hostname, int port)
{
	struct sockaddr_in serv_addr;
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	struct hostent *server;
	if (sockfd < 0)
		error("ERROR opening socket");
	server = gethostbyname(hostname);
	if (server == NULL) {
		fprintf(stderr,"ERROR, no such host\n");
		exit(0);
	}
	bzero((char *) &serv_addr, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	memcpy(&serv_addr.sin_addr.s_addr,server->h_addr,server->h_length);
	serv_addr.sin_port = htons(port);
	if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
		error("ERROR connecting");
	/* at this point, should be able to send/recv on sockfd */
	//! Handshake 
	//! Client -- SYN ---> Server
	size_t SYN = rand() % 69420 + 100000;
	if (send(sockfd, &SYN,sizeof(SYN),0) == -1){
		error("failed to send SYN");
	}

	//! Server -- SYN+1, ACK ---> Server
	char buffer[256];
	if (recv(sockfd, buffer, sizeof(buffer), 0) == -1) {
	    error("failed to receive message");
	}
	
	string message(buffer);
	size_t delimiter = message.find(",");
	if (delimiter == string::npos) {
	    error("invalid message format");
	}
	string test_syn = message.substr(0, delimiter);
	string ack = message.substr(delimiter + 1);

	//! Client -- ACK ---> Server
	if (stoi(test_syn) == SYN+1){
		if (send(sockfd, ack.c_str(), ack.size() ,0) == -1){
			error("failed to send ACK");
		}
	}
	else exit(0);
	//! Handshake

	// TODO Diffie Hellman
	// init("params");
	// NEWZ(a);
	// NEWZ(A);
	// dhGen(a,A);
	// NEWZ(B);
	// If A,a long term key, read from file
	// If ephemeral, this is fine
	// if B is long term, read from file, otherwise, get from network.
	// See Z2BYTES macro...
	// Once you have it, run dhFinal on a,A,B... This will compute the shared secret
	// and do key derivation
	// size_t pklen = mpz_size(A);
	// const size_t klen = 128;
	// unsigned char kA[klen];
	// dhFinal(a,A,B,kA,klen);

	// if (send(sockfd, A, pklen,0)== -1){
    //     error("ERROR sending DH public key");
	// }

	// const size_t buflen = 4;
	// char buf[buflen];
	// if (recv(sockfd, buf, buflen, 0) == -1) {
	//     error("ERROR receiving acknowledgment message");
	// }
	// if (strcmp(buf, "ACK") != 0) {
	//     error("ERROR: unexpected acknowledgment message");
	// }

	return 0;
}

static int shutdownNetwork()
{
	shutdown(sockfd,2);
	unsigned char dummy[64];
	ssize_t r;
	do {
		r = recv(sockfd,dummy,64,0);
	} while (r != 0 && r != -1);
	close(sockfd);
	return 0;
}

/* end network stuff. */


[[noreturn]] static void fail_exit(const char *msg)
{
	// Make sure endwin() is only called in visual mode. As a note, calling it
	// twice does not seem to be supported and messed with the cursor position.
	if (!isendwin())
		endwin();
	fprintf(stderr, "%s\n", msg);
	exit(EXIT_FAILURE);
}

// Checks errors for (most) ncurses functions. CHECK(fn, x, y, z) is a checked
// version of fn(x, y, z).
#define CHECK(fn, ...) \
	do \
	if (fn(__VA_ARGS__) == ERR) \
	fail_exit(#fn"("#__VA_ARGS__") failed"); \
	while (false)

static bool should_exit = false;

// Message window
static WINDOW *msg_win;
// Separator line above the command (readline) window
static WINDOW *sep_win;
// Command (readline) window
static WINDOW *cmd_win;

// Input character for readline
static unsigned char input;

static int readline_getc(FILE *dummy)
{
	return input;
}

/* if batch is set, don't draw immediately to real screen (use wnoutrefresh
 * instead of wrefresh) */
static void msg_win_redisplay(bool batch, const string& newmsg="", const string& sender="")
{
	if (batch)
		wnoutrefresh(msg_win);
	else {
		wattron(msg_win,COLOR_PAIR(2));
		wprintw(msg_win,"%s:",sender.c_str());
		wattroff(msg_win,COLOR_PAIR(2));
		wprintw(msg_win," %s\n",newmsg.c_str());
		wrefresh(msg_win);
	}
}

static void msg_typed(char *line)
{
	string mymsg;
	if (!line) {
		// Ctrl-D pressed on empty line
		should_exit = true;
		/* XXX send a "goodbye" message so other end doesn't
		 * have to wait for timeout on recv()? */
	} else {
	// TODO: this is where your message will be processed to send to the other party.  You should encrypt and mac before sending!  (your message is in variable 'line' btw)
	// Andy
		RSA* keys = RSA_new();
		if(!keys) exit(1);
		BIGNUM* e = BN_new();
		if (!e) exit(1);
		BN_set_word(e,RSA_F4); // This is how you set e to RSA_F4 which is 65537

		// Now to generate the RSA key call 
		int check_r = RSA_generate_key_ex(keys,2048,e,NULL);
		// RSA_generate_key_ex which will return 0 if it fails and 1 if the key was generated
		if (check_r != 1) exit(1);

		// Now write the Public key in RSA and store it in stdout as a PEM(Privately Enchanced Mail)
		// PEM_write_RSA_PUBKEY(stdout, keys);
		// Private KEY
		// PEM_write_RSAPrivateKey(stdout,keys,NULL,NULL,0,NULL,NULL);

		// Encrypt the message by getting the msg which is line and the size of the RSA key
		size_t len = strlen(line); // Length of the message
		unsigned char* ct = (unsigned char*)malloc(RSA_size(keys)); // allocate dynamic memory for the RSA key
		int ctlen = RSA_public_encrypt(len+1, (unsigned char*)line, ct, keys,RSA_PKCS1_OAEP_PADDING); // RSA_PKCS1_OAEP_PADDING is used to add more inputs to make the encryption better
		if (ctlen == -1) exit(1);

		//! MAC
		char* shared_key = "Mactest";
		unsigned char mac[32];
		memset(mac,0,32);
		HMAC(EVP_sha256(), shared_key, strlen(shared_key), (unsigned char*)line, len, mac, NULL);
		//! MAC created
		
		
		//TODO: Concatonate mac + ct
		unsigned char* mac_ct = (unsigned char*)malloc(ctlen+32); // Alocate Memory for mac + ct
		memcpy(mac_ct,mac,32); // Add mac to the beginning of mac_ct
		memcpy(mac_ct + 32, ct, ctlen); // Adds ct to mac_ct after the 32 location



	// Andy	
		if (*line) {
			add_history(line);
			mymsg = string(line);
			transcript.push_back("me: " + mymsg);
			ssize_t nbytes;
			if ((nbytes = send(sockfd,mac_ct,ctlen + 32,0)) == -1)
				error("send failed");
		}

		//! Original ====
		// if (*line) {
			// add_history(line);
			// mymsg = string(line);
			// transcript.push_back("me: " + mymsg);
			// ssize_t nbytes;
			// if ((nbytes = send(sockfd,line,mymsg.length(),0)) == -1)
				// error("send failed");
		// }
		//! Original ====
		
		pthread_mutex_lock(&qmx);
		mq.push_back({false,mymsg,"me",msg_win});
		pthread_cond_signal(&qcv);
		pthread_mutex_unlock(&qmx);
	}
}

/* if batch is set, don't draw immediately to real screen (use wnoutrefresh
 * instead of wrefresh) */
static void cmd_win_redisplay(bool batch)
{
	int prompt_width = strnlen(rl_display_prompt, 128);
	int cursor_col = prompt_width + strnlen(rl_line_buffer,rl_point);

	werase(cmd_win);
	mvwprintw(cmd_win, 0, 0, "%s%s", rl_display_prompt, rl_line_buffer);
	/* XXX deal with a longer message than the terminal window can show */
	if (cursor_col >= COLS) {
		// Hide the cursor if it lies outside the window. Otherwise it'll
		// appear on the very right.
		curs_set(0);
	} else {
		wmove(cmd_win,0,cursor_col);
		curs_set(1);
	}
	if (batch)
		wnoutrefresh(cmd_win);
	else
		wrefresh(cmd_win);
}

static void readline_redisplay(void)
{
	pthread_mutex_lock(&qmx);
	mq.push_back({false,"","",cmd_win});
	pthread_cond_signal(&qcv);
	pthread_mutex_unlock(&qmx);
}

static void resize(void)
{
	if (LINES >= 3) {
		wresize(msg_win,LINES-2,COLS);
		wresize(sep_win,1,COLS);
		wresize(cmd_win,1,COLS);
		/* now move bottom two to last lines: */
		mvwin(sep_win,LINES-2,0);
		mvwin(cmd_win,LINES-1,0);
	}

	/* Batch refreshes and commit them with doupdate() */
	msg_win_redisplay(true);
	wnoutrefresh(sep_win);
	cmd_win_redisplay(true);
	doupdate();
}

static void init_ncurses(void)
{
	if (!initscr())
		fail_exit("Failed to initialize ncurses");

	if (has_colors()) {
		CHECK(start_color);
		CHECK(use_default_colors);
	}
	CHECK(cbreak);
	CHECK(noecho);
	CHECK(nonl);
	CHECK(intrflush, NULL, FALSE);

	curs_set(1);

	if (LINES >= 3) {
		msg_win = newwin(LINES - 2, COLS, 0, 0);
		sep_win = newwin(1, COLS, LINES - 2, 0);
		cmd_win = newwin(1, COLS, LINES - 1, 0);
	} else {
		// Degenerate case. Give the windows the minimum workable size to
		// prevent errors from e.g. wmove().
		msg_win = newwin(1, COLS, 0, 0);
		sep_win = newwin(1, COLS, 0, 0);
		cmd_win = newwin(1, COLS, 0, 0);
	}
	if (!msg_win || !sep_win || !cmd_win)
		fail_exit("Failed to allocate windows");

	scrollok(msg_win,true);

	if (has_colors()) {
		// Use white-on-blue cells for the separator window...
		CHECK(init_pair, 1, COLOR_WHITE, COLOR_BLUE);
		CHECK(wbkgd, sep_win, COLOR_PAIR(1));
		/* NOTE: -1 is the default background color, which for me does
		 * not appear to be any of the normal colors curses defines. */
		CHECK(init_pair, 2, COLOR_MAGENTA, -1);
	}
	else {
		wbkgd(sep_win,A_STANDOUT); /* c.f. man curs_attr */
	}
	wrefresh(sep_win);
}

static void deinit_ncurses(void)
{
	delwin(msg_win);
	delwin(sep_win);
	delwin(cmd_win);
	endwin();
}

static void init_readline(void)
{
	// Let ncurses do all terminal and signal handling
	rl_catch_signals = 0;
	rl_catch_sigwinch = 0;
	rl_deprep_term_function = NULL;
	rl_prep_term_function = NULL;

	// Prevent readline from setting the LINES and COLUMNS environment
	// variables, which override dynamic size adjustments in ncurses. When
	// using the alternate readline interface (as we do here), LINES and
	// COLUMNS are not updated if the terminal is resized between two calls to
	// rl_callback_read_char() (which is almost always the case).
	rl_change_environment = 0;

	// Handle input by manually feeding characters to readline
	rl_getc_function = readline_getc;
	rl_redisplay_function = readline_redisplay;

	rl_callback_handler_install("> ", msg_typed);
}

static void deinit_readline(void)
{
	rl_callback_handler_remove();
}

static const char* usage =
"Usage: %s [OPTIONS]...\n"
"Secure chat for CSc380.\n\n"
"   -c, --connect HOST  Attempt a connection to HOST.\n"
"   -l, --listen        Listen for new connections.\n"
"   -p, --port    PORT  Listen or connect on PORT (defaults to 1337).\n"
"   -h, --help          show this message and exit.\n";

int main(int argc, char *argv[])
{
	// define long options
	static struct option long_opts[] = {
		{"connect",  required_argument, 0, 'c'},
		{"listen",   no_argument,       0, 'l'},
		{"port",     required_argument, 0, 'p'},
		{"help",     no_argument,       0, 'h'},
		{0,0,0,0}
	};
	// process options:
	char c;
	int opt_index = 0;
	int port = 1337;
	char hostname[HOST_NAME_MAX+1] = "localhost";
	hostname[HOST_NAME_MAX] = 0;
	bool isclient = true;

	while ((c = getopt_long(argc, argv, "c:lp:h", long_opts, &opt_index)) != -1) {
		switch (c) {
			case 'c':
				if (strnlen(optarg,HOST_NAME_MAX))
					strncpy(hostname,optarg,HOST_NAME_MAX);
				break;
			case 'l':
				isclient = false;
				break;
			case 'p':
				port = atoi(optarg);
				break;
			case 'h':
				printf(usage,argv[0]);
				return 0;
			case '?':
				printf(usage,argv[0]);
				return 1;
		}
	}
	if (isclient) {
		initClientNet(hostname,port);
	} else {
		initServerNet(port);
	}

	/* NOTE: these don't work if called from cursesthread */
	init_ncurses();
	init_readline();
	/* start curses thread */
	if (pthread_create(&tcurses,0,cursesthread,0)) {
		fprintf(stderr, "Failed to create curses thread.\n");
	}
	/* start receiver thread: */
	if (pthread_create(&trecv,0,recvMsg,0)) {
		fprintf(stderr, "Failed to create update thread.\n");
	}

	/* put this in the queue to signal need for resize: */
	redraw_data rd = {false,"","",NULL};
	do {
		int c = wgetch(cmd_win);
		switch (c) {
			case KEY_RESIZE:
				pthread_mutex_lock(&qmx);
				mq.push_back(rd);
				pthread_cond_signal(&qcv);
				pthread_mutex_unlock(&qmx);
				break;
				// Ctrl-L -- redraw screen
			// case '\f':
			// 	// Makes the next refresh repaint the screen from scratch
			// 	/* XXX this needs to be done in the curses thread as well. */
			// 	clearok(curscr,true);
			// 	resize();
			// 	break;
			default:
				input = c;
				rl_callback_read_char();
		}
	} while (!should_exit);

	shutdownNetwork();
	deinit_ncurses();
	deinit_readline();
	return 0;
}

/* Let's have one thread responsible for all things curses.  It should
 * 1. Initialize the library
 * 2. Wait for messages (we'll need a mutex-protected queue)
 * 3. Restore terminal / end curses mode? */

/* We'll need yet another thread to listen for incoming messages and
 * post them to the queue. */

void* cursesthread(void* pData)
{
	/* NOTE: these calls only worked from the main thread... */
	// init_ncurses();
	// init_readline();
	while (true) {
		pthread_mutex_lock(&qmx);
		while (mq.empty()) {
			pthread_cond_wait(&qcv,&qmx);
			/* NOTE: pthread_cond_wait will release the mutex and block, then
			 * reaquire it before returning.  Given that only one thread (this
			 * one) consumes elements of the queue, we probably don't have to
			 * check in a loop like this, but in general this is the recommended
			 * way to do it.  See the man page for details. */
		}
		/* at this point, we have control of the queue, which is not empty,
		 * so write all the messages and then let go of the mutex. */
		while (!mq.empty()) {
			redraw_data m = mq.front();
			mq.pop_front();
			if (m.win == cmd_win) {
				cmd_win_redisplay(m.resize);
			} else if (m.resize) {
				resize();
			} else {
				msg_win_redisplay(false,m.msg,m.sender);
				/* Redraw input window to "focus" it (otherwise the cursor
				 * will appear in the transcript which is confusing). */
				cmd_win_redisplay(false);
			}
		}
		pthread_mutex_unlock(&qmx);
	}
	return 0;
}

void* recvMsg(void*)
{
	size_t maxlen = 256;
	char msg[maxlen+1];
	ssize_t nbytes;
	while (1) {
		if ((nbytes = recv(sockfd,msg,maxlen,0)) == -1)
			error("recv failed");
		msg[nbytes] = 0; /* make sure it is null-terminated */
		if (nbytes == 0) {
			/* signal to the main loop that we should quit: */
			should_exit = true;
			return 0;
		}
		// TODO: you have just received an encrypted message.
		// Check the MAC, decrypt, and post to the curses thread
		// for drawing (add decrypted message to mq
		// might want to format messages to include the length
		// so you can know if you read the whole thing.
		// char* pt = malloc(ctlen);
		// size_t ptlen = RSA_private_decrypt(ctlen,ct,(unsigned char*)pt,keys,RSA_PKCS1_OAEP_PADDING);
		// if (ptlen == -1) exit(1);

		pthread_mutex_lock(&qmx);
		mq.push_back({false,msg,"Mr Thread",msg_win});
		pthread_cond_signal(&qcv);
		pthread_mutex_unlock(&qmx);
	}
	return 0;
}
