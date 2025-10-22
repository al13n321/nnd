#include <signal.h>
#include <stdio.h>

static int count = 0;

void signalHandler(int) {
    if (count == 0)
        printf("received signal\n");
    count += 1;
}

int main() {
    struct sigaction sa = {0};
    sa.sa_handler = signalHandler;
    if (sigaction(SIGUSR1, &sa, NULL) == -1) {
        perror("sigaction");
        return 1;
    }

    while (count < 100000)
        raise(SIGUSR1);

    printf("bye\n");

    return 0;
}
