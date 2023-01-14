int main()
//@ requires true;
//@ ensures true;
{
struct stack *s = create_stack();
stack_push(s, 10);
stack_push(s, 20);
stack_pop(s);
stack_pop(s);
stack_dispose(s);
return 0;
}