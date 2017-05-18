	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_ge25519_nielsadd2
	.globl	crypto_sign_ed25519_amd64_64_ge25519_nielsadd2
_crypto_sign_ed25519_amd64_64_ge25519_nielsadd2:
crypto_sign_ed25519_amd64_64_ge25519_nielsadd2:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$128, %rsp
	movq	32(%rdi), %rax
	movq	40(%rdi), %rcx
	movq	48(%rdi), %rdx
	movq	56(%rdi), %r8
	movq	%rax, %r11
	movq	%rcx, %rbp
	movq	%rdx, %rbx
	movq	%r8, %r12
	subq	(%rdi), %rax
	sbbq	8(%rdi), %rcx
	sbbq	16(%rdi), %rdx
	sbbq	24(%rdi), %r8
	movq	$0, %r9
	movq	$38, %r10
	cmovnbq	%r9, %r10
	subq	%r10, %rax
	sbbq	%r9, %rcx
	sbbq	%r9, %rdx
	sbbq	%r9, %r8
	cmovbq	%r10, %r9
	subq	%r9, %rax
	addq	(%rdi), %r11
	adcq	8(%rdi), %rbp
	adcq	16(%rdi), %rbx
	adcq	24(%rdi), %r12
	movq	$0, %r9
	movq	$38, %r10
	cmovnbq	%r9, %r10
	addq	%r10, %r11
	adcq	%r9, %rbp
	adcq	%r9, %rbx
	adcq	%r9, %r12
	cmovbq	%r10, %r9
	addq	%r9, %r11
	movq	%rax, (%rsp)
	movq	%rcx, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%r8, 24(%rsp)
	movq	%r11, 32(%rsp)
	movq	%rbp, 40(%rsp)
	movq	%rbx, 48(%rsp)
	movq	%r12, 56(%rsp)
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r13
	movq	(%rsp), %rcx
	movq	(%rsi), %rax
	mulq	%rcx
	movq	%rax, %r14
	movq	%rdx, %r8
	movq	8(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	16(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	24(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsp), %rcx
	movq	(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	8(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	16(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	24(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	adcq	%rdx, %rbx
	movq	16(%rsp), %rcx
	movq	(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	8(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	16(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	24(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	adcq	%rdx, %r12
	movq	24(%rsp), %rcx
	movq	(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	8(%rsi), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbp, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	16(%rsi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	24(%rsi), %rax
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
	movq	%r14, (%rsp)
	movq	%r8, 8(%rsp)
	movq	%r9, 16(%rsp)
	movq	%r10, 24(%rsp)
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r13
	movq	32(%rsp), %rcx
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
	movq	40(%rsp), %rcx
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
	movq	48(%rsp), %rcx
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
	movq	56(%rsp), %rcx
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
	movq	%r14, %rdx
	movq	%r8, %r11
	movq	%r9, %rbp
	movq	%r10, %rbx
	subq	(%rsp), %r14
	sbbq	8(%rsp), %r8
	sbbq	16(%rsp), %r9
	sbbq	24(%rsp), %r10
	movq	$0, %rax
	movq	$38, %rcx
	cmovnbq	%rax, %rcx
	subq	%rcx, %r14
	sbbq	%rax, %r8
	sbbq	%rax, %r9
	sbbq	%rax, %r10
	cmovbq	%rcx, %rax
	subq	%rax, %r14
	addq	(%rsp), %rdx
	adcq	8(%rsp), %r11
	adcq	16(%rsp), %rbp
	adcq	24(%rsp), %rbx
	movq	$0, %rax
	movq	$38, %rcx
	cmovnbq	%rax, %rcx
	addq	%rcx, %rdx
	adcq	%rax, %r11
	adcq	%rax, %rbp
	adcq	%rax, %rbx
	cmovbq	%rcx, %rax
	addq	%rax, %rdx
	movq	%rdx, (%rsp)
	movq	%r11, 8(%rsp)
	movq	%rbp, 16(%rsp)
	movq	%rbx, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%r8, 40(%rsp)
	movq	%r9, 48(%rsp)
	movq	%r10, 56(%rsp)
	movq	$0, %r11
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r13
	movq	96(%rdi), %rcx
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
	movq	104(%rdi), %rcx
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
	movq	112(%rdi), %rcx
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
	movq	120(%rdi), %rcx
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
	movq	64(%rdi), %rax
	movq	72(%rdi), %rcx
	movq	80(%rdi), %rdx
	movq	88(%rdi), %rsi
	addq	%rax, %rax
	adcq	%rcx, %rcx
	adcq	%rdx, %rdx
	adcq	%rsi, %rsi
	movq	$0, %r11
	movq	$38, %rbp
	cmovnbq	%r11, %rbp
	addq	%rbp, %rax
	adcq	%r11, %rcx
	adcq	%r11, %rdx
	adcq	%r11, %rsi
	cmovbq	%rbp, %r11
	addq	%r11, %rax
	movq	%rax, %rbx
	movq	%rcx, %r12
	movq	%rdx, %r13
	movq	%rsi, %r15
	subq	%r14, %rax
	sbbq	%r8, %rcx
	sbbq	%r9, %rdx
	sbbq	%r10, %rsi
	movq	$0, %r11
	movq	$38, %rbp
	cmovnbq	%r11, %rbp
	subq	%rbp, %rax
	sbbq	%r11, %rcx
	sbbq	%r11, %rdx
	sbbq	%r11, %rsi
	cmovbq	%rbp, %r11
	subq	%r11, %rax
	addq	%r14, %rbx
	adcq	%r8, %r12
	adcq	%r9, %r13
	adcq	%r10, %r15
	movq	$0, %r8
	movq	$38, %r9
	cmovnbq	%r8, %r9
	addq	%r9, %rbx
	adcq	%r8, %r12
	adcq	%r8, %r13
	adcq	%r8, %r15
	cmovbq	%r9, %r8
	addq	%r8, %rbx
	movq	%rbx, 64(%rsp)
	movq	%r12, 72(%rsp)
	movq	%r13, 80(%rsp)
	movq	%r15, 88(%rsp)
	movq	%rax, 96(%rsp)
	movq	%rcx, 104(%rsp)
	movq	%rdx, 112(%rsp)
	movq	%rsi, 120(%rsp)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	32(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	40(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	48(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	56(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, (%rdi)
	movq	%rsi, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%r9, 24(%rdi)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	8(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	16(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	24(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, 32(%rdi)
	movq	%rsi, 40(%rdi)
	movq	%r8, 48(%rdi)
	movq	%r9, 56(%rdi)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	64(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	72(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	80(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	88(%rsp), %rcx
	movq	96(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	104(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	112(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	120(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, 64(%rdi)
	movq	%rsi, 72(%rdi)
	movq	%r8, 80(%rdi)
	movq	%r9, 88(%rdi)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	32(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	40(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	48(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	56(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, 96(%rdi)
	movq	%rsi, 104(%rdi)
	movq	%r8, 112(%rdi)
	movq	%r9, 120(%rdi)
	addq	$128, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
