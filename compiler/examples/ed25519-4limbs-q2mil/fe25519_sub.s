	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_fe25519_sub
	.globl	crypto_sign_ed25519_amd64_64_fe25519_sub
_crypto_sign_ed25519_amd64_64_fe25519_sub:
crypto_sign_ed25519_amd64_64_fe25519_sub:
	pushq	%rbp
	pushq	%rsi
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %rsi
	subq	(%rdx), %rax
	sbbq	8(%rdx), %rcx
	sbbq	16(%rdx), %r8
	sbbq	24(%rdx), %rsi
	movq	$0, %rdx
	movq	$38, %r9
	cmovnbq	%rdx, %r9
	subq	%r9, %rax
	sbbq	%rdx, %rcx
	sbbq	%rdx, %r8
	sbbq	%rdx, %rsi
	cmovbq	%r9, %rdx
	subq	%rdx, %rax
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%rsi, 24(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
