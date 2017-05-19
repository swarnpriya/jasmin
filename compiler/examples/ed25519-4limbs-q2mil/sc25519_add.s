	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_sc25519_add
	.globl	crypto_sign_ed25519_amd64_64_sc25519_add
_crypto_sign_ed25519_amd64_64_sc25519_add:
crypto_sign_ed25519_amd64_64_sc25519_add:
	pushq	%rbp
	pushq	%rsi
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %rsi
	addq	(%rdx), %rax
	adcq	8(%rdx), %rcx
	adcq	16(%rdx), %r8
	adcq	24(%rdx), %rsi
	movq	%rax, %rdx
	movq	%rcx, %r9
	movq	%r8, %r10
	movq	%rsi, %r11
	subq	$6346243789798364141, %rdx
	sbbq	$1503914060200516822, %r9
	sbbq	$0, %r10
	sbbq	$1152921504606846976, %r11
	cmovnbq	%rdx, %rax
	cmovnbq	%r9, %rcx
	cmovnbq	%r10, %r8
	cmovnbq	%r11, %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%rsi, 24(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
