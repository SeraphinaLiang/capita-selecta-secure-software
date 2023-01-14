//Annotations by Yinqi Liang (R0865008) Master of Engineering : Computer Science

#include <limits.h>
#include <stdio.h>
#include "stdlib.h"
#include "stringBuffers.h"
#include "threading.h"
#include "sockets.h"


struct email {
  struct string_buffer* body;
  struct email* next;
};

struct account {
  struct string_buffer* username;
  struct string_buffer* password;
  struct email* inbox;
  int nb_messages;
  struct account* next;
};

struct database {
  struct account* head;
  struct mutex* mutex;
};

struct session {
  struct socket* socket;
  struct database* db;
};



/*@
predicate_family_instance thread_run_data(handle_connection)(struct session *sess) =
  sess->db |-> ?db &*& 
  sess->socket |-> ?socket &*& 
  malloc_block_session(sess) &*& 
  socket(socket) &*&
  [?d]database_predicate(db);
 
predicate_ctor db_pre(struct database *db)() =  db->head |-> _ ;

predicate database_predicate(struct database* db) =
  db !=0 &*&
  malloc_block_database(db) &*&
  db->mutex |-> ?mutex &*&
  mutex(mutex,db_pre(db)) &*&
  db->head |-> ?head &*&
  account_predicate(head);

predicate email_predicate(struct email *e) =
    e == 0? true :
    (malloc_block_email(e) &*&
    e->body |-> ?body &*&
    string_buffer(body) &*&
    e->next |-> ?next &*&
    email_predicate(next));

predicate account_predicate(struct account* a) =
  a == 0 ? true :
  (malloc_block_account(a) &*&
  a->username |-> ?username &*&
  a->password |-> ?password &*&
  a->nb_messages |-> ?nb_messages &*&
  a->inbox |-> ?inbox &*&
  a->next |-> ?next &*&
  string_buffer(username) &*&
  string_buffer(password) &*&
  0 <= nb_messages &*&
  email_predicate(inbox) &*&
  account_predicate(next));

@*/


void account_dispose(struct account* a)
{
  
  struct email* curr = a->inbox;
  while(curr != 0)
  {
    struct email* tmp = curr->next;
    string_buffer_dispose(curr->body);
    free(curr);
    curr = tmp;
  }
  string_buffer_dispose(a->username);
  string_buffer_dispose(a->password);
  free(a);
}

bool accounts_contains(struct account* a, struct string_buffer* username)
{
  if(a == 0) {
    return false;
  } else {
    bool found = string_buffer_equals(a->username, username);
    if(found) {
      return true;
    } else {
      return accounts_contains(a->next, username);
    }
  }
}

int create_account(struct database* db, struct string_buffer* username, struct string_buffer* password)
//@ requires [?d]database_predicate(db) &*& string_buffer(username) &*& string_buffer(password);
//@ ensures [d]database_predicate(db) &*& string_buffer(username) &*& string_buffer(password);
{
  bool username_taken;
  struct account* a = malloc(sizeof(struct account));
  if(a == 0) return -1;
  a->username = username;
  a->password = password;
  a->inbox = 0;
  a->nb_messages = 0;
  //@ open [d]database_predicate(db);
  mutex_acquire(db->mutex);
  //@ open db_pre(db)();
  username_taken = accounts_contains(db->head, username);
  if(username_taken) {
    mutex_release(db->mutex);
    free(a);
    return -2;
  }
  a->next = db->head;
  db->head = a;
  //@ close db_pre(db)();
  mutex_release(db->mutex);
  //@ close [d]database_predicate(db);
  return 0;
}

int send_mail_core(struct account* a, struct string_buffer* to, struct email* e)
{
  if(a == 0) {
    return -2;
  } else {
    bool found = string_buffer_equals(a->username, to);
    if(found) {
      if(a->nb_messages <= 1000) {
        e->next = a->inbox;
        a->inbox = e;
        a->nb_messages = a->nb_messages + 1;
        return 0;
      } else {
        return -3;
      }
    } else {
      return send_mail_core(a->next, to, e);
    }
  }
}

int send_mail(struct database* db, struct string_buffer* to, struct string_buffer* body)
//@ requires [?d]database_predicate(db) &*& [?o]string_buffer(to) &*& [?u]string_buffer(body);
//@ ensures [d]database_predicate(db) &*& [o]string_buffer(to) &*& [u]string_buffer(body);
{
  int res;
  struct email* e = malloc(sizeof(struct email));
  if(e == 0) return -1;
  e->body = body;
  //@ open [d]database_predicate(db);
  mutex_acquire(db->mutex);
  //@ open db_pre(db)();
  res = send_mail_core(db->head, to, e);
  //@ close db_pre(db)();
  mutex_release(db->mutex);
  //@ close [d]database_predicate(db);
  if(res != 0) {
    free(e);
  } else {
    string_buffer_dispose(to);
  }
  return res;
}

void write_mails_to_buffer(struct email* e, struct string_buffer* buf)
{
  if(e == 0) {
  } else {
    write_mails_to_buffer(e->next, buf);
    string_buffer_append_string_buffer(buf, e->body);
    string_buffer_append_string(buf, "\r\n");
  }
}

int read_mail_core(struct account* a, struct string_buffer* buf, struct string_buffer* username, struct string_buffer* password)
{
  if(a == 0) {
    return -1;
  } else {
    bool found = string_buffer_equals(a->username, username);
    if(found) {
      bool password_correct = string_buffer_equals(a->password, password);
      if(password_correct) {
        string_buffer_append_string(buf, "You have ");
        string_buffer_append_integer_as_decimal(buf, a->nb_messages);
        string_buffer_append_string(buf, " messages:\r\n");
        write_mails_to_buffer(a->inbox, buf);
        return 0;
      } else {
        return -2;
      }
    } else {
      return read_mail_core(a->next, buf, username, password);
    }
  }
}

int read_mail(struct database* db, struct string_buffer* output, struct string_buffer* username, struct string_buffer* password)
//@ requires [?d]database_predicate(db) &*& [?o]string_buffer(output) &*& [?u]string_buffer(username)  &*& [?p]string_buffer(password);
//@ ensures [d]database_predicate(db) &*& [o]string_buffer(output) &*& [u]string_buffer(username)  &*& [p]string_buffer(password);
{
  int res;
  //@ open [d]database_predicate(db);
  mutex_acquire(db->mutex);
  //@ open db_pre(db)();
  res = read_mail_core(db->head, output, username, password);
  //@ close db_pre(db)();
  mutex_release(db->mutex);
  //@ close [d]database_predicate(db);
  return res;
}

void show_user_names(struct database* db, struct string_buffer* buf)
//@ requires [?d]database_predicate(db) &*& [?b]string_buffer(buf);
//@ ensures [d]database_predicate(db) &*& [b]string_buffer(buf);
{
  struct account* curr;
  //@ open [d]database_predicate(db);
  mutex_acquire(db->mutex);
  //@ open db_pre(db)();
  curr = db->head;
  while(curr != 0) // Hint: consider using a loop contract
  //@ invariant [d]database_predicate(db) &*& [b]string_buffer(buf);
  {
    string_buffer_append_string_buffer(buf, curr->username);
    string_buffer_append_string(buf, "\r\n");
    curr = curr->next;
  }
  //@ close db_pre(db)();
  mutex_release(db->mutex);
  //@ close [d]database_predicate(db);
}

void show_menu(struct socket* s)
//@ requires socket(s);
//@ ensures socket(s);
{
  socket_write_string(s, "1. create account\r\n");
  socket_write_string(s, "2. send mail\r\n");
  socket_write_string(s, "3. read mail\r\n");
  socket_write_string(s, "4. show all user names\r\n");
  socket_write_string(s, "5. quit\r\n");
}

void main_menu(struct socket* s, struct database* db)
//@ requires socket(s) &*& [?d]database_predicate(db);
//@ ensures true;
{
  int choice;
  socket_write_string(s, "welcome!\r\n");
  show_menu(s);
  choice = socket_read_nonnegative_integer(s);
  while(choice != 5) 
  //@ invariant socket(s) &*& [d]database_predicate(db);
  {
    int res;
    if(choice == 1) {
      struct string_buffer* username = create_string_buffer();
      struct string_buffer* password = create_string_buffer();
      socket_write_string(s, "enter username\r\n");
      socket_read_line(s, username);
      socket_write_string(s, "enter password\r\n");
      socket_read_line(s, password);
      res = create_account(db, username, password);
      if(res == 0) {
       //@leak string_buffer(password);
       //@leak string_buffer(username);
        socket_write_string(s, "account created\r\n");
      } else {
        string_buffer_dispose(username);
        string_buffer_dispose(password);
        if(res == -1) {
          socket_write_string(s, "insufficient memory\r\n");
        } else {
          socket_write_string(s, "username already in use\r\n");
        }
      }
    } else if(choice == 2) {
      struct string_buffer* to = create_string_buffer();
      struct string_buffer* body = create_string_buffer();
      socket_write_string(s, "enter to\r\n");
      socket_read_line(s, to);
      socket_write_string(s, "enter body\r\n");
      socket_read_line(s, body);
      res = send_mail(db, to, body);
      if(res == 0) {
       //@leak string_buffer(to);
       //@leak string_buffer(body);
        socket_write_string(s, "mail sent\r\n");
      } else {
        string_buffer_dispose(body);
        string_buffer_dispose(to);
        if(res == -1) {
          socket_write_string(s, "insufficient memory\r\n");
        } else if(res == -2) {
          socket_write_string(s, "user not found\r\n");
        } else {
          socket_write_string(s, "user inbox full\r\n");
        }
      }
    } else if(choice == 3) {
      struct string_buffer* username = create_string_buffer();
      struct string_buffer* password = create_string_buffer();
      struct string_buffer* buf = create_string_buffer();
      socket_write_string(s, "enter username\r\n");
      socket_read_line(s, username);
      socket_write_string(s, "enter password\r\n");
      socket_read_line(s, password);
      res = read_mail(db, buf, username, password);
      if(res == 0) {
        socket_write_string_buffer(s, buf);
      } else if(res == -1) {
        socket_write_string(s, "bad username\r\n");
      } else {
        socket_write_string(s, "wrong password\r\n");
      }
      string_buffer_dispose(username);
      string_buffer_dispose(password);
      string_buffer_dispose(buf);
    } else if(choice == 4) {
      struct string_buffer* buf = create_string_buffer();
      show_user_names(db, buf);
      socket_write_string_buffer(s, buf);
      string_buffer_dispose(buf);
    } else {
      socket_write_string(s, "invalid choice, try again\r\n");
    }
    show_menu(s);
    choice = socket_read_nonnegative_integer(s);
  }
  socket_write_string(s, "bye!\r\n");
  socket_close(s);
  //@ leak [_]database_predicate(db);
}

void handle_connection(struct session* session)//@ : thread_run
//@ requires thread_run_data(handle_connection)(session);
//@ ensures true;
{
  //@ open thread_run_data(handle_connection)(session);
  main_menu(session->socket, session->db);
  free(session);
}

/*@
lemma void helper(struct database* db);
    requires emp;
    ensures [?d]database_predicate(db);
@*/

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct server_socket* ss;
  struct mutex* mutex;
  struct database* db = malloc(sizeof(struct database));
  if(db == 0) abort();
  db->head = 0;
  //@ close db_pre(db)();
  //@ close create_mutex_ghost_arg(db_pre(db));
  mutex = create_mutex();
  db->mutex = mutex;
  ss = create_server_socket(1234);
  //@ helper(db);
  while(true)
  //@ invariant server_socket(ss) &*& [?d]database_predicate(db);
  {
    struct socket* s = server_socket_accept(ss);
    struct session* session = malloc(sizeof(struct session));
    if(session == 0) {
      socket_write_string(s, "insufficient memory\r\n");
      socket_close(s);
    } else {
      session->socket = s;
      session->db = db;
      //@ close thread_run_data(handle_connection)(session);
      thread_start(handle_connection, session);
      //@ helper(db);
    }
  } 
}
