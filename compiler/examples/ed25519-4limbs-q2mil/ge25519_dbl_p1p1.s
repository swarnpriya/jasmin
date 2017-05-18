	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_ge25519_dbl_p1p1
	.globl	crypto_sign_ed25519_amd64_64_ge25519_dbl_p1p1
_crypto_sign_ed25519_amd64_64_ge25519_dbl_p1p1:
crypto_sign_ed25519_amd64_64_ge25519_dbl_p1p1:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$128, %rsp
	movq	$0, %rbp
	movq	8(%rsi), %rax
	mulq	(%rsi)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	16(%rsi), %rax
	mulq	8(%rsi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	24(%rsi), %rax
	mulq	16(%rsi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	16(%rsi), %rax
	mulq	(%rsi)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	24(%rsi), %rax
	mulq	8(%rsi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	24(%rsi), %rax
	mulq	(%rsi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	(%rsi), %rax
	mulq	(%rsi)
	movq	%rax, %r15
	movq	%rdx, %r12
	movq	8(%rsi), %rax
	mulq	8(%rsi)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	16(%rsi), %rax
	mulq	16(%rsi)
	addq	%r12, %rbx
	adcq	%r13, %rcx
	adcq	%r14, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	24(%rsi), %rax
	mulq	24(%rsi)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	%r9, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r9
	movq	%r10, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%rbp, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r9, %r15
	adcq	%r10, %rbx
	adcq	%r11, %rcx
	adcq	%rbp, %r8
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rdx, %rbx
	adcq	%rdx, %rcx
	adcq	%rdx, %r8
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r15
	movq	%r15, (%rsp)
	movq	%rbx, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%r8, 24(%rsp)
	movq	$0, %rbp
	movq	40(%rsi), %rax
	mulq	32(%rsi)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	48(%rsi), %rax
	mulq	40(%rsi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	56(%rsi), %rax
	mulq	48(%rsi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	48(%rsi), %rax
	mulq	32(%rsi)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	56(%rsi), %rax
	mulq	40(%rsi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	56(%rsi), %rax
	mulq	32(%rsi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	32(%rsi), %rax
	mulq	32(%rsi)
	movq	%rax, %r15
	movq	%rdx, %r12
	movq	40(%rsi), %rax
	mulq	40(%rsi)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	48(%rsi), %rax
	mulq	48(%rsi)
	addq	%r12, %rbx
	adcq	%r13, %rcx
	adcq	%r14, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	56(%rsi), %rax
	mulq	56(%rsi)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	%r9, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r9
	movq	%r10, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%rbp, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r9, %r15
	adcq	%r10, %rbx
	adcq	%r11, %rcx
	adcq	%rbp, %r8
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rdx, %rbx
	adcq	%rdx, %rcx
	adcq	%rdx, %r8
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r15
	movq	%r15, 32(%rsp)
	movq	%rbx, 40(%rsp)
	movq	%rcx, 48(%rsp)
	movq	%r8, 56(%rsp)
	movq	$0, %rbp
	movq	72(%rsi), %rax
	mulq	64(%rsi)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	80(%rsi), %rax
	mulq	72(%rsi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	88(%rsi), %rax
	mulq	80(%rsi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	80(%rsi), %rax
	mulq	64(%rsi)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	88(%rsi), %rax
	mulq	72(%rsi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	88(%rsi), %rax
	mulq	64(%rsi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	64(%rsi), %rax
	mulq	64(%rsi)
	movq	%rax, %r15
	movq	%rdx, %r12
	movq	72(%rsi), %rax
	mulq	72(%rsi)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	80(%rsi), %rax
	mulq	80(%rsi)
	addq	%r12, %rbx
	adcq	%r13, %rcx
	adcq	%r14, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	88(%rsi), %rax
	mulq	88(%rsi)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	%r9, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r9
	movq	%r10, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%rbp, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r9, %r15
	adcq	%r10, %rbx
	adcq	%r11, %rcx
	adcq	%rbp, %r8
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rdx, %rbx
	adcq	%rdx, %rcx
	adcq	%rdx, %r8
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r15
	addq	%r15, %r15
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	movq	$0, %rax
	movq	$38, %rdx
	cmovnbq	%rax, %rdx
	addq	%rdx, %r15
	adcq	%rax, %rbx
	adcq	%rax, %rcx
	adcq	%rax, %r8
	cmovbq	%rdx, %rax
	addq	%rax, %r15
	movq	%r15, 64(%rsp)
	movq	%rbx, 72(%rsp)
	movq	%rcx, 80(%rsp)
	movq	%r8, 88(%rsp)
	movq	$0, %rax
	movq	$0, %rcx
	movq	$0, %rdx
	movq	$0, %r8
	subq	(%rsp), %rax
	sbbq	8(%rsp), %rcx
	sbbq	16(%rsp), %rdx
	sbbq	24(%rsp), %r8
	movq	$0, %r9
	movq	$38, %r10
	cmovnbq	%r9, %r10
	subq	%r10, %rax
	sbbq	%r9, %rcx
	sbbq	%r9, %rdx
	sbbq	%r9, %r8
	cmovbq	%r10, %r9
	subq	%r9, %rax
	movq	%rax, (%rsp)
	movq	%rcx, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%r8, 24(%rsp)
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	subq	32(%rsp), %r9
	sbbq	40(%rsp), %r10
	sbbq	48(%rsp), %r11
	sbbq	56(%rsp), %rbp
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	subq	%r12, %r9
	sbbq	%rbx, %r10
	sbbq	%rbx, %r11
	sbbq	%rbx, %rbp
	cmovbq	%r12, %rbx
	subq	%rbx, %r9
	movq	%r9, 96(%rsp)
	movq	%r10, 104(%rsp)
	movq	%r11, 112(%rsp)
	movq	%rbp, 120(%rsp)
	movq	%rax, %r9
	movq	%rcx, %r10
	movq	%rdx, %r11
	movq	%r8, %rbp
	addq	32(%rsp), %r9
	adcq	40(%rsp), %r10
	adcq	48(%rsp), %r11
	adcq	56(%rsp), %rbp
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	addq	%r12, %r9
	adcq	%rbx, %r10
	adcq	%rbx, %r11
	adcq	%rbx, %rbp
	cmovbq	%r12, %rbx
	addq	%rbx, %r9
	movq	%r9, 32(%rdi)
	movq	%r10, 40(%rdi)
	movq	%r11, 48(%rdi)
	movq	%rbp, 56(%rdi)
	subq	32(%rsp), %rax
	sbbq	40(%rsp), %rcx
	sbbq	48(%rsp), %rdx
	sbbq	56(%rsp), %r8
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	subq	%r12, %rax
	sbbq	%rbx, %rcx
	sbbq	%rbx, %rdx
	sbbq	%rbx, %r8
	cmovbq	%r12, %rbx
	subq	%rbx, %rax
	movq	%rax, 64(%rdi)
	movq	%rcx, 72(%rdi)
	movq	%rdx, 80(%rdi)
	movq	%r8, 88(%rdi)
	subq	64(%rsp), %r9
	sbbq	72(%rsp), %r10
	sbbq	80(%rsp), %r11
	sbbq	88(%rsp), %rbp
	movq	$0, %rax
	movq	$38, %rcx
	cmovnbq	%rax, %rcx
	subq	%rcx, %r9
	sbbq	%rax, %r10
	sbbq	%rax, %r11
	sbbq	%rax, %rbp
	cmovbq	%rcx, %rax
	subq	%rax, %r9
	movq	%r9, 96(%rdi)
	movq	%r10, 104(%rdi)
	movq	%r11, 112(%rdi)
	movq	%rbp, 120(%rdi)
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %rdx
	movq	24(%rsi), %r8
	addq	32(%rsi), %rax
	adcq	40(%rsi), %rcx
	adcq	48(%rsi), %rdx
	adcq	56(%rsi), %r8
	movq	$0, %rsi
	movq	$38, %r9
	cmovnbq	%rsi, %r9
	addq	%r9, %rax
	adcq	%rsi, %rcx
	adcq	%rsi, %rdx
	adcq	%rsi, %r8
	cmovbq	%r9, %rsi
	addq	%rsi, %rax
	movq	%rax, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	%r8, 56(%rsp)
	movq	$0, %r11
	movq	40(%rsp), %rax
	mulq	32(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	48(%rsp), %rax
	mulq	40(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	56(%rsp), %rax
	mulq	48(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	48(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	56(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	56(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	addq	%rbp, %rbp
	adcq	%rcx, %rcx
	adcq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	movq	32(%rsp), %rax
	mulq	32(%rsp)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	40(%rsp), %rax
	mulq	40(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	48(%rsp), %rax
	mulq	48(%rsp)
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	56(%rsp), %rax
	mulq	56(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	%r8, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r9, %rax
	movq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	%r10, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r14
	adcq	%r9, %rbp
	adcq	%r10, %rcx
	adcq	%r11, %rsi
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rdx, %rbp
	adcq	%rdx, %rcx
	adcq	%rdx, %rsi
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r14
	addq	(%rsp), %r14
	adcq	8(%rsp), %rbp
	adcq	16(%rsp), %rcx
	adcq	24(%rsp), %rsi
	movq	$0, %rax
	movq	$38, %rdx
	cmovnbq	%rax, %rdx
	addq	%rdx, %r14
	adcq	%rax, %rbp
	adcq	%rax, %rcx
	adcq	%rax, %rsi
	cmovbq	%rdx, %rax
	addq	%rax, %r14
	addq	96(%rsp), %r14
	adcq	104(%rsp), %rbp
	adcq	112(%rsp), %rcx
	adcq	120(%rsp), %rsi
	movq	$0, %rax
	movq	$38, %rdx
	cmovnbq	%rax, %rdx
	addq	%rdx, %r14
	adcq	%rax, %rbp
	adcq	%rax, %rcx
	adcq	%rax, %rsi
	cmovbq	%rdx, %rax
	addq	%rax, %r14
	movq	%r14, (%rdi)
	movq	%rbp, 8(%rdi)
	movq	%rcx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	addq	$128, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
