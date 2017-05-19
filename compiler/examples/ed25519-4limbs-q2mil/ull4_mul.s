	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_ull4_mul
	.globl	crypto_sign_ed25519_amd64_64_ull4_mul
_crypto_sign_ed25519_amd64_64_ull4_mul:
crypto_sign_ed25519_amd64_64_ull4_mul:
	pushq	%rbp
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	movq	%rdx, %rcx
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	$0, %r15
	movq	$0, %r8
	movq	(%rsi), %rax
	mulq	(%rcx)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	(%rsi), %rax
	mulq	8(%rcx)
	movq	%rax, %r11
	addq	%r10, %r11
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	(%rsi), %rax
	mulq	16(%rcx)
	movq	%rax, %rbp
	addq	%r10, %rbp
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	(%rsi), %rax
	mulq	24(%rcx)
	movq	%rax, %rbx
	addq	%r10, %rbx
	adcq	%rdx, %r12
	movq	8(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %r11
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	8(%rsi), %rax
	mulq	8(%rcx)
	addq	%rax, %rbp
	adcq	%r8, %rdx
	addq	%r10, %rbp
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	8(%rsi), %rax
	mulq	16(%rcx)
	addq	%rax, %rbx
	adcq	%r8, %rdx
	addq	%r10, %rbx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	8(%rsi), %rax
	mulq	24(%rcx)
	addq	%rax, %r12
	adcq	%r8, %rdx
	addq	%r10, %r12
	adcq	%rdx, %r13
	movq	16(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %rbp
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	16(%rsi), %rax
	mulq	8(%rcx)
	addq	%rax, %rbx
	adcq	%r8, %rdx
	addq	%r10, %rbx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	16(%rsi), %rax
	mulq	16(%rcx)
	addq	%rax, %r12
	adcq	%r8, %rdx
	addq	%r10, %r12
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	16(%rsi), %rax
	mulq	24(%rcx)
	addq	%rax, %r13
	adcq	%r8, %rdx
	addq	%r10, %r13
	adcq	%rdx, %r14
	movq	24(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %rbx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	24(%rsi), %rax
	mulq	8(%rcx)
	addq	%rax, %r12
	adcq	%r8, %rdx
	addq	%r10, %r12
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	24(%rsi), %rax
	mulq	16(%rcx)
	addq	%rax, %r13
	adcq	%r8, %rdx
	addq	%r10, %r13
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	24(%rsi), %rax
	mulq	24(%rcx)
	addq	%rax, %r14
	adcq	%r8, %rdx
	addq	%r10, %r14
	adcq	%rdx, %r15
	movq	%r9, (%rdi)
	movq	%r11, 8(%rdi)
	movq	%rbp, 16(%rdi)
	movq	%rbx, 24(%rdi)
	movq	%r12, 32(%rdi)
	movq	%r13, 40(%rdi)
	movq	%r14, 48(%rdi)
	movq	%r15, 56(%rdi)
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rbp
	ret 
