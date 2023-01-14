char getchar();
void putchar(char c);
int main()
{
char c1 = getchar();
char c2 = getchar();
char c3 = getchar();
char c4 = getchar();
char c5 = getchar();
for (int i = 0; i < 2; i++) {
putchar(c1);
putchar(c2);
putchar(c3);
putchar(c4);
putchar(c5);
}
return 0;
}