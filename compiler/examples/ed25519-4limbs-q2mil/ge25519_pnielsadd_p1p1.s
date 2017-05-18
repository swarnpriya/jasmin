	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_ge25519_pnielsadd_p1p1
	.globl	crypto_sign_ed25519_amd64_64_ge25519_pnielsadd_p1p1
_crypto_sign_ed25519_amd64_64_ge25519_pnielsadd_p1p1:
crypto_sign_ed25519_amd64_64_ge25519_pnielsadd_p1p1:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$64, %rsp
	movq	%rdx, %rcx
	movq	32(%rsi), %rax
	movq	40(%rsi), %rdx
	movq	48(%rsi), %r8
	movq	56(%rsi), %r9
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	%r8, %r12
	movq	%r9, %r13
	subq	(%rsi), %rax
	sbbq	8(%rsi), %rdx
	sbbq	16(%rsi), %r8
	sbbq	24(%rsi), %r9
	movq	$0, %r10
	movq	$38, %r11
	cmovnbq	%r10, %r11
	subq	%r11, %rax
	sbbq	%r10, %rdx
	sbbq	%r10, %r8
	sbbq	%r10, %r9
	cmovbq	%r11, %r10
	subq	%r10, %rax
	addq	(%rsi), %rbp
	adcq	8(%rsi), %rbx
	adcq	16(%rsi), %r12
	adcq	24(%rsi), %r13
	movq	$0, %r10
	movq	$38, %r11
	cmovnbq	%r10, %r11
	addq	%r11, %rbp
	adcq	%r10, %rbx
	adcq	%r10, %r12
	adcq	%r10, %r13
	cmovbq	%r11, %r10
	addq	%r10, %rbp
	movq	%rax, (%rsp)
	movq	%rdx, 8(%rsp)
	movq	%r8, 16(%rsp)
	movq	%r9, 24(%rsp)
	movq	%rbp, 32(%rsp)
	movq	%rbx, 40(%rsp)
	movq	%r12, 48(%rsp)
	movq	%r13, 56(%rsp)
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	(%rsp), %r8
	movq	(%rcx), %rax
	mulq	%r8
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	8(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	16(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	8(%rsp), %r8
	movq	(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	8(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	16(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	24(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	16(%rsp), %r8
	movq	(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	8(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	16(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	24(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	24(%rsp), %r8
	movq	(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	8(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	16(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	24(%rcx), %rax
	mulq	%r8
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14
	movq	%rbp, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r12, %rax
	movq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%r13, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%rbp, %r9
	adcq	%rbx, %r10
	adcq	%r12, %r11
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rdx, %r9
	adcq	%rdx, %r10
	adcq	%rdx, %r11
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r15
	movq	%r15, (%rsp)
	movq	%r9, 8(%rsp)
	movq	%r10, 16(%rsp)
	movq	%r11, 24(%rsp)
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	32(%rsp), %r8
	movq	32(%rcx), %rax
	mulq	%r8
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	40(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	48(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	56(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	40(%rsp), %r8
	movq	32(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	40(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	48(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	56(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	48(%rsp), %r8
	movq	32(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	40(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	48(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	56(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	56(%rsp), %r8
	movq	32(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	40(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	48(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	56(%rcx), %rax
	mulq	%r8
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14
	movq	%rbp, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r12, %rax
	movq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%r13, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%rbp, %r9
	adcq	%rbx, %r10
	adcq	%r12, %r11
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rdx, %r9
	adcq	%rdx, %r10
	adcq	%rdx, %r11
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r15
	movq	%r15, %rax
	movq	%r9, %rdx
	movq	%r10, %r8
	movq	%r11, %rbp
	addq	(%rsp), %rax
	adcq	8(%rsp), %rdx
	adcq	16(%rsp), %r8
	adcq	24(%rsp), %rbp
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	addq	%r12, %rax
	adcq	%rbx, %rdx
	adcq	%rbx, %r8
	adcq	%rbx, %rbp
	cmovbq	%r12, %rbx
	addq	%rbx, %rax
	subq	(%rsp), %r15
	sbbq	8(%rsp), %r9
	sbbq	16(%rsp), %r10
	sbbq	24(%rsp), %r11
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	subq	%r12, %r15
	sbbq	%rbx, %r9
	sbbq	%rbx, %r10
	sbbq	%rbx, %r11
	cmovbq	%r12, %rbx
	subq	%rbx, %r15
	movq	%r15, (%rdi)
	movq	%r9, 8(%rdi)
	movq	%r10, 16(%rdi)
	movq	%r11, 24(%rdi)
	movq	%rax, 64(%rdi)
	movq	%rdx, 72(%rdi)
	movq	%r8, 80(%rdi)
	movq	%rbp, 88(%rdi)
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	96(%rsi), %r8
	movq	96(%rcx), %rax
	mulq	%r8
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	104(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	112(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	120(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	104(%rsi), %r8
	movq	96(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	104(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	112(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	120(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	112(%rsi), %r8
	movq	96(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	104(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	112(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	120(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	120(%rsi), %r8
	movq	96(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	104(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	112(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	120(%rcx), %rax
	mulq	%r8
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14
	movq	%rbp, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r12, %rax
	movq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%r13, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%rbp, %r9
	adcq	%rbx, %r10
	adcq	%r12, %r11
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rdx, %r9
	adcq	%rdx, %r10
	adcq	%rdx, %r11
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r15
	movq	%r15, (%rsp)
	movq	%r9, 8(%rsp)
	movq	%r10, 16(%rsp)
	movq	%r11, 24(%rsp)
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	64(%rsi), %r8
	movq	64(%rcx), %rax
	mulq	%r8
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	72(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	80(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	72(%rsi), %r8
	movq	64(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	80(%rsi), %r8
	movq	64(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	88(%rsi), %rsi
	movq	64(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r11
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	72(%rcx), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r8, %rbp
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	80(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r8, %r12
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	88(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%r8, %r13
	adcq	%rdx, %r14
	movq	%rbp, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%r12, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r13, %rax
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r14, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%rsi, %r9
	adcq	%r8, %r10
	adcq	%rbp, %r11
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	addq	%r15, %r15
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	movq	$0, %rax
	movq	$38, %rcx
	cmovnbq	%rax, %rcx
	addq	%rcx, %r15
	adcq	%rax, %r9
	adcq	%rax, %r10
	adcq	%rax, %r11
	cmovbq	%rcx, %rax
	addq	%rax, %r15
	movq	%r15, %rax
	movq	%r9, %rcx
	movq	%r10, %rdx
	movq	%r11, %rsi
	addq	(%rsp), %rax
	adcq	8(%rsp), %rcx
	adcq	16(%rsp), %rdx
	adcq	24(%rsp), %rsi
	movq	$0, %r8
	movq	$38, %rbp
	cmovnbq	%r8, %rbp
	addq	%rbp, %rax
	adcq	%r8, %rcx
	adcq	%r8, %rdx
	adcq	%r8, %rsi
	cmovbq	%rbp, %r8
	addq	%r8, %rax
	subq	(%rsp), %r15
	sbbq	8(%rsp), %r9
	sbbq	16(%rsp), %r10
	sbbq	24(%rsp), %r11
	movq	$0, %r8
	movq	$38, %rbp
	cmovnbq	%r8, %rbp
	subq	%rbp, %r15
	sbbq	%r8, %r9
	sbbq	%r8, %r10
	sbbq	%r8, %r11
	cmovbq	%rbp, %r8
	subq	%r8, %r15
	movq	%rax, 32(%rdi)
	movq	%rcx, 40(%rdi)
	movq	%rdx, 48(%rdi)
	movq	%rsi, 56(%rdi)
	movq	%r15, 96(%rdi)
	movq	%r9, 104(%rdi)
	movq	%r10, 112(%rdi)
	movq	%r11, 120(%rdi)
	addq	$64, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
