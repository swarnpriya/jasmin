	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_sc25519_lt
	.globl	crypto_sign_ed25519_amd64_64_sc25519_lt
_crypto_sign_ed25519_amd64_64_sc25519_lt:
crypto_sign_ed25519_amd64_64_sc25519_lt:
	pushq	%rbp
	pushq	%rdi
	movq	(%rdi), %rax
	movq	8(%rdi), %rcx
	movq	16(%rdi), %rdx
	movq	24(%rdi), %rdi
	subq	(%rsi), %rax
	sbbq	8(%rsi), %rcx
	sbbq	16(%rsi), %rdx
	sbbq	24(%rsi), %rdi
	movq	$0, %rax
	movq	$1, %rcx
	cmovbq	%rcx, %rax
	popq	%rdi
	popq	%rbp
	ret 
