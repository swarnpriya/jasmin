	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_sc25519_sub_nored
	.globl	crypto_sign_ed25519_amd64_64_sc25519_sub_nored
_crypto_sign_ed25519_amd64_64_sc25519_sub_nored:
crypto_sign_ed25519_amd64_64_sc25519_sub_nored:
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
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%rsi, 24(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
