#ifndef SOCKETS_H
#define SOCKETS_H

#include <stdbool.h>
#include <stdlib.h>
#include "stringBuffers.h"

struct server_socket;
struct socket;

/*@
predicate server_socket(struct server_socket *serverSocket);
predicate socket(struct socket *socket);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires emp;
    //@ ensures server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& socket(result);
void socket_write_string(struct socket* socket, char* string);
    //@ requires socket(socket) &*& [?f]string(string, ?cs);
    //@ ensures socket(socket) &*& [f]string(string, cs);
void socket_write_string_buffer(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket(socket) &*& [?f]string_buffer(buffer);
    //@ ensures socket(socket) &*& [f]string_buffer(buffer);
void socket_write_integer_as_decimal(struct socket *socket, int value);
    //@ requires socket(socket);
    //@ ensures socket(socket);
void socket_read_line(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket(socket) &*& string_buffer(buffer);
    //@ ensures socket(socket) &*& string_buffer(buffer);
char* socket_read_line_as_string(struct socket* socket);
    //@ requires socket(socket);
    //@ ensures socket(socket) &*& result == 0 ? true : string(result, ?cs) &*& malloc_block(result, length(cs) + 1);
int socket_read_nonnegative_integer(struct socket *socket);
    //@ requires socket(socket);
    //@ ensures socket(socket);

void socket_close(struct socket *socket);
    //@ requires socket(socket);
    //@ ensures emp;

#endif
