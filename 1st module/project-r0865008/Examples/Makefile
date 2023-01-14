HELLO = hello.elf
HELLO_BIN = hello.bin
HELLO_IHEX = hello.ihex

ASM = asm.elf
ASM_BIN = asm.bin
ASM_IHEX = asm.ihex

.SECONDARY:

all: $(HELLO_BIN) $(HELLO_IHEX) $(ASM_BIN) $(ASM_IHEX)

KERNEL_DIR = ../Tools/Kernel
include $(KERNEL_DIR)/Makefile.include

asm.elf: asm.o
	$(CC) -ffreestanding -nostdlib -T standalone.ld -o $@ $^

clean: clean_kernel
	rm -f $(HELLO) $(HELLO:.elf=.o) $(HELLO_BIN) $(HELLO_IHEX) $(ASM) $(ASM:.elf=.o) $(ASM_BIN) $(ASM_IHEX)
