        .weakref foobar, barfnot

#if (defined(__FreeBSD__) || defined(__linux__)) && defined(__ELF__)
    .section .note.GNU-stack,"",@progbits
#endif
