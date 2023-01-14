#include "stdlib.h"
struct account {
int balance;
};

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account_balance(myAccount, _);
//@ ensures account_balance(myAccount, newBalance);
{
myAccount->balance = newBalance;
}

int account_get_balance(struct account *myAccount)
//@ requires account_balance(myAccount, _);
//@ ensures account_balance(myAccount, _);
{
return myAccount->balance;
}

int main()
//@ requires true;
//@ ensures true;
{
struct account *myAccount = malloc(sizeof(struct account));
account_set_balance(myAccount, 5);
int b = account_get_balance(myAccount);
assert(b == 5);
account_dispose(myAccount);
return 0;
}