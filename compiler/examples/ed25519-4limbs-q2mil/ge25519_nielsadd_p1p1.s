	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_ge25519_nielsadd_p1p1
	.globl	crypto_sign_ed25519_amd64_64_ge25519_nielsadd_p1p1
_crypto_sign_ed25519_amd64_64_ge25519_nielsadd_p1p1:
crypto_sign_ed25519_amd64_64_ge25519_nielsadd_p1p1:
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
	movq	%r15, %r8
	movq	%r9, %rbp
	movq	%r10, %rbx
	movq	%r11, %r12
	subq	(%rsp), %r15
	sbbq	8(%rsp), %r9
	sbbq	16(%rsp), %r10
	sbbq	24(%rsp), %r11
	movq	$0, %rax
	movq	$38, %rdx
	cmovnbq	%rax, %rdx
	subq	%rdx, %r15
	sbbq	%rax, %r9
	sbbq	%rax, %r10
	sbbq	%rax, %r11
	cmovbq	%rdx, %rax
	subq	%rax, %r15
	addq	(%rsp), %r8
	adcq	8(%rsp), %rbp
	adcq	16(%rsp), %rbx
	adcq	24(%rsp), %r12
	movq	$0, %rax
	movq	$38, %rdx
	cmovnbq	%rax, %rdx
	addq	%rdx, %r8
	adcq	%rax, %rbp
	adcq	%rax, %rbx
	adcq	%rax, %r12
	cmovbq	%rdx, %rax
	addq	%rax, %r8
	movq	%r8, 64(%rdi)
	movq	%rbp, 72(%rdi)
	movq	%rbx, 80(%rdi)
	movq	%r12, 88(%rdi)
	movq	%r15, (%rdi)
	movq	%r9, 8(%rdi)
	movq	%r10, 16(%rdi)
	movq	%r11, 24(%rdi)
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	96(%rsi), %r8
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
	movq	104(%rsi), %r8
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
	movq	112(%rsi), %r8
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
	movq	120(%rsi), %r8
	movq	64(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rcx), %rax
	mulq	%r8
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14
	movq	%rbp, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%r12, %rax
	movq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r13, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%r14, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r8, %r9
	adcq	%rbp, %r10
	adcq	%rbx, %r11
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
	movq	64(%rsi), %rax
	movq	72(%rsi), %rcx
	movq	80(%rsi), %rdx
	movq	88(%rsi), %rsi
	addq	%rax, %rax
	adcq	%rcx, %rcx
	adcq	%rdx, %rdx
	adcq	%rsi, %rsi
	movq	$0, %r8
	movq	$38, %rbp
	cmovnbq	%r8, %rbp
	addq	%rbp, %rax
	adcq	%r8, %rcx
	adcq	%r8, %rdx
	adcq	%r8, %rsi
	cmovbq	%rbp, %r8
	addq	%r8, %rax
	movq	%rax, %rbx
	movq	%rcx, %r12
	movq	%rdx, %r13
	movq	%rsi, %r14
	subq	%r15, %rax
	sbbq	%r9, %rcx
	sbbq	%r10, %rdx
	sbbq	%r11, %rsi
	movq	$0, %r8
	movq	$38, %rbp
	cmovnbq	%r8, %rbp
	subq	%rbp, %rax
	sbbq	%r8, %rcx
	sbbq	%r8, %rdx
	sbbq	%r8, %rsi
	cmovbq	%rbp, %r8
	subq	%r8, %rax
	addq	%r15, %rbx
	adcq	%r9, %r12
	adcq	%r10, %r13
	adcq	%r11, %r14
	movq	$0, %r8
	movq	$38, %r9
	cmovnbq	%r8, %r9
	addq	%r9, %rbx
	adcq	%r8, %r12
	adcq	%r8, %r13
	adcq	%r8, %r14
	cmovbq	%r9, %r8
	addq	%r8, %rbx
	movq	%rbx, 32(%rdi)
	movq	%r12, 40(%rdi)
	movq	%r13, 48(%rdi)
	movq	%r14, 56(%rdi)
	movq	%rax, 96(%rdi)
	movq	%rcx, 104(%rdi)
	movq	%rdx, 112(%rdi)
	movq	%rsi, 120(%rdi)
	addq	$64, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
