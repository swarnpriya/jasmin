	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_ge25519_p1p1_to_p3
	.globl	crypto_sign_ed25519_amd64_64_ge25519_p1p1_to_p3
_crypto_sign_ed25519_amd64_64_ge25519_p1p1_to_p3:
crypto_sign_ed25519_amd64_64_ge25519_p1p1_to_p3:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r13
	movq	(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	movq	%rax, %r14
	movq	%rdx, %r8
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	adcq	%rdx, %rbx
	movq	16(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	adcq	%rdx, %r12
	movq	24(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbp, %r12
	adcq	%rdx, %r13
	movq	%r11, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbx, %rax
	movq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%r13, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r14
	adcq	%r11, %r8
	adcq	%rbp, %r9
	adcq	%rbx, %r10
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r14
	movq	%r14, (%rdi)
	movq	%r8, 8(%rdi)
	movq	%r9, 16(%rdi)
	movq	%r10, 24(%rdi)
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r13
	movq	64(%rsi), %rcx
	movq	32(%rsi), %rax
	mulq	%rcx
	movq	%rax, %r14
	movq	%rdx, %r8
	movq	40(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	48(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	56(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	72(%rsi), %rcx
	movq	32(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	40(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	48(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	56(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	adcq	%rdx, %rbx
	movq	80(%rsi), %rcx
	movq	32(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	40(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	48(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	56(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	adcq	%rdx, %r12
	movq	88(%rsi), %rcx
	movq	32(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	40(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	48(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	56(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbp, %r12
	adcq	%rdx, %r13
	movq	%r11, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbx, %rax
	movq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%r13, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r14
	adcq	%r11, %r8
	adcq	%rbp, %r9
	adcq	%rbx, %r10
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r14
	movq	%r14, 32(%rdi)
	movq	%r8, 40(%rdi)
	movq	%r9, 48(%rdi)
	movq	%r10, 56(%rdi)
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r13
	movq	32(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	movq	%rax, %r14
	movq	%rdx, %r8
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	40(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	adcq	%rdx, %rbx
	movq	48(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	adcq	%rdx, %r12
	movq	56(%rsi), %rcx
	movq	96(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	104(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	112(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	120(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbp, %r12
	adcq	%rdx, %r13
	movq	%r11, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbx, %rax
	movq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%r13, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r14
	adcq	%r11, %r8
	adcq	%rbp, %r9
	adcq	%rbx, %r10
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r14
	movq	%r14, 64(%rdi)
	movq	%r8, 72(%rdi)
	movq	%r9, 80(%rdi)
	movq	%r10, 88(%rdi)
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r13
	movq	(%rsi), %rcx
	movq	64(%rsi), %rax
	mulq	%rcx
	movq	%rax, %r14
	movq	%rdx, %r8
	movq	72(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	80(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	88(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsi), %rcx
	movq	64(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	72(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	80(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	88(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	adcq	%rdx, %rbx
	movq	16(%rsi), %rcx
	movq	64(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	72(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	80(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	88(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	adcq	%rdx, %r12
	movq	24(%rsi), %rcx
	movq	64(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	72(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	80(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	88(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbp, %r12
	adcq	%rdx, %r13
	movq	%r11, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbx, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r12, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r13, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r14
	adcq	%rsi, %r8
	adcq	%r11, %r9
	adcq	%rbp, %r10
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r14
	movq	%r14, 96(%rdi)
	movq	%r8, 104(%rdi)
	movq	%r9, 112(%rdi)
	movq	%r10, 120(%rdi)
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
