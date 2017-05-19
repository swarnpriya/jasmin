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
	movq	%rax, %r9
	movq	%rcx, %r10
	movq	%r8, %r11
	movq	%rsi, %rbp
	movq	$6346243789798364141, %rdx
	subq	%rdx, %r9
	movq	$1503914060200516822, %rdx
	sbbq	%rdx, %r10
	movq	$0, %rdx
	sbbq	%rdx, %r11
	movq	$1152921504606846976, %rdx
	sbbq	%rdx, %rbp
	cmovnbq	%r9, %rax
	cmovnbq	%r10, %rcx
	cmovnbq	%r11, %r8
	cmovnbq	%rbp, %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%rsi, 24(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
