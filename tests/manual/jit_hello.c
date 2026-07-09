#define _GNU_SOURCE

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

typedef void (*jit_fn_t)(void);

int main(void) {
    const char message[] = "hello world\n";

    // x86-64 Linux:
    //   mov eax, 1          ; SYS_write
    //   mov edi, 1          ; stdout
    //   lea rsi, [rip+disp] ; message
    //   mov edx, len
    //   syscall
    //   ret
    uint8_t code_template[] = {
        0xb8, 0x01, 0x00, 0x00, 0x00,
        0xbf, 0x01, 0x00, 0x00, 0x00,
        0x48, 0x8d, 0x35, 0x00, 0x00, 0x00, 0x00,
        0xba, 0x00, 0x00, 0x00, 0x00,
        0x0f, 0x05,
        0xc3,
    };

    const size_t page_size = (size_t)sysconf(_SC_PAGESIZE);
    void *mem = mmap(NULL, page_size, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

    const size_t code_size = sizeof(code_template);
    const size_t message_size = sizeof(message) - 1;
    uint8_t *code = (uint8_t *)mem;
    uint8_t *message_dst = code + code_size;

    memcpy(code, code_template, code_size);
    memcpy(message_dst, message, message_size);

    const size_t lea_disp_offset = 13;
    const size_t lea_next_ip_offset = 17;
    int32_t lea_disp = (int32_t)(message_dst - (code + lea_next_ip_offset));
    memcpy(code + lea_disp_offset, &lea_disp, sizeof(lea_disp));

    const size_t len_offset = 18;
    uint32_t len = (uint32_t)message_size;
    memcpy(code + len_offset, &len, sizeof(len));

    mprotect(mem, page_size, PROT_READ | PROT_EXEC);

    printf("jit code address: %p\n", (void *)code);
    fflush(stdout);

    ((jit_fn_t)code)();

    return 0;
}
