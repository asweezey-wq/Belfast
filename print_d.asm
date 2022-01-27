_printd:
        mov  r9, -3689348814741910323
        sub     rsp, 40
        mov     BYTE [rsp+31], 10
        lea     rcx, [rsp+30]
.L2:
        ; Divide rdi by 10, store in rdx
        mov     rax, rdi
        lea     r8, [rsp+32]
        mul     r9
        mov     rax, rdi
        sub     r8, rcx
        shr     rdx, 3
        lea     rsi, [rdx+rdx*4]
        add     rsi, rsi
        sub     rax, rsi
        ; RAX = (RDI - RDX * 10) = RDI % 10
        add     eax, 48
        mov     BYTE [rcx], al
        ; Put '0' + RAX at end of buffer (rcx)
        mov     rax, rdi
        ; store i in rax
        mov     rdi, rdx
        ; i = i / 10 (rdi = rdx)
        mov     rdx, rcx
        ; store buffer ptr in rdx
        sub     rcx, 1
        ; subtract 1 from buffer ptr
        cmp     rax, 9
        ; continue looping if i >= 10
        ja      .L2
        lea     rax, [rsp+32]
        mov     edi, 1
        sub     rdx, rax
        xor     eax, eax
        lea     rsi, [rsp+32+rdx]
        ; RSI = RSP + 32 + (BUFFER PTR - (RSP + 32))
        ; RSI = BUFFER_PTR
        mov     rdx, r8
        ; R8 = RSP + 32 - BUFFER_PTR
        mov     rax, 0x2000004
        syscall
        add     rsp, 40
        ret