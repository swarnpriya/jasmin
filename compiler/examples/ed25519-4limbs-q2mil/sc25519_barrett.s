	.text
	.p2align	5
	.globl	_crypto_sign_ed25519_amd64_64_sc25519_barrett
	.globl	crypto_sign_ed25519_amd64_64_sc25519_barrett
_crypto_sign_ed25519_amd64_64_sc25519_barrett:
crypto_sign_ed25519_amd64_64_sc25519_barrett:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	subq	$32, %rsp
	xorq	%rcx, %rcx
	xorq	%r8, %r8
	xorq	%r9, %r9
	xorq	%r10, %r10
	xorq	%r11, %r11
	movq	24(%rsi), %rax
	movq	$-1, %rdx
	mulq	%rdx
	movq	%rax, %r12
	movq	%rdx, %rbp
	movq	24(%rsi), %rax
	movq	$15, %rdx
	mulq	%rdx
	movq	%rax, %rbx
	addq	%rbp, %rbx
	adcq	%rdx, %r8
	movq	32(%rsi), %rax
	movq	$-21, %rdx
	mulq	%rdx
	addq	%rax, %r12
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	32(%rsi), %rax
	movq	$-1, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	adcq	%rcx, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	32(%rsi), %rax
	movq	$15, %rdx
	mulq	%rdx
	addq	%rax, %r8
	adcq	%rcx, %rdx
	addq	%rbp, %r8
	adcq	%rdx, %r9
	movq	40(%rsi), %rax
	movq	$2379626136568277415, %rdx
	mulq	%rdx
	addq	%rax, %r12
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	40(%rsi), %rax
	movq	$-21, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	adcq	%rcx, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	40(%rsi), %rax
	movq	$-1, %rdx
	mulq	%rdx
	addq	%rax, %r8
	adcq	%rcx, %rdx
	addq	%rbp, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	40(%rsi), %rax
	movq	$15, %rdx
	mulq	%rdx
	addq	%rax, %r9
	adcq	%rcx, %rdx
	addq	%rbp, %r9
	adcq	%rdx, %r10
	movq	48(%rsi), %rax
	movq	$-1324931701940677861, %rdx
	mulq	%rdx
	addq	%rax, %r12
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	48(%rsi), %rax
	movq	$2379626136568277415, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	adcq	%rcx, %rdx
	addq	%rbp, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	48(%rsi), %rax
	movq	$-21, %rdx
	mulq	%rdx
	addq	%rax, %r8
	adcq	%rcx, %rdx
	addq	%rbp, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	48(%rsi), %rax
	movq	$-1, %rdx
	mulq	%rdx
	addq	%rax, %r9
	adcq	%rcx, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	48(%rsi), %rax
	movq	$15, %rdx
	mulq	%rdx
	addq	%rax, %r10
	adcq	%rcx, %rdx
	addq	%rbp, %r10
	adcq	%rdx, %r11
	movq	56(%rsi), %rax
	movq	$-1324931701940677861, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	56(%rsi), %rax
	movq	$2379626136568277415, %rdx
	mulq	%rdx
	addq	%rax, %r8
	adcq	%rcx, %rdx
	addq	%rbp, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	%r8, (%rsp)
	movq	56(%rsi), %rax
	movq	$-21, %rdx
	mulq	%rdx
	addq	%rax, %r9
	adcq	%rcx, %rdx
	addq	%rbp, %r9
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r9, 8(%rsp)
	movq	56(%rsi), %rax
	movq	$-1, %rdx
	mulq	%rdx
	addq	%rax, %r10
	adcq	%rcx, %rdx
	addq	%r8, %r10
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r10, 16(%rsp)
	movq	56(%rsi), %rax
	movq	$15, %rdx
	mulq	%rdx
	addq	%rax, %r11
	adcq	%rcx, %rdx
	addq	%r8, %r11
	movq	%r11, 24(%rsp)
	movq	(%rsp), %rax
	movq	$6346243789798364141, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	(%rsp), %rax
	movq	$1503914060200516822, %rdx
	mulq	%rdx
	movq	%rax, %r10
	addq	%r9, %r10
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	(%rsp), %rax
	movq	$0, %rdx
	mulq	%rdx
	movq	%rax, %r11
	addq	%r9, %r11
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	(%rsp), %rax
	movq	$1152921504606846976, %rdx
	mulq	%rdx
	movq	%rax, %rbp
	addq	%r9, %rbp
	movq	8(%rsp), %rax
	movq	$6346243789798364141, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	8(%rsp), %rax
	movq	$1503914060200516822, %rdx
	mulq	%rdx
	addq	%rax, %r11
	adcq	%rcx, %rdx
	addq	%r9, %r11
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	8(%rsp), %rax
	movq	$0, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	addq	%rcx, %rbp
	movq	16(%rsp), %rax
	movq	$6346243789798364141, %rcx
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	16(%rsp), %rax
	movq	$1503914060200516822, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	addq	%rcx, %rbp
	movq	24(%rsp), %rax
	movq	$6346243789798364141, %rcx
	mulq	%rcx
	addq	%rax, %rbp
	movq	(%rsi), %rax
	subq	%r8, %rax
	movq	%rax, %r9
	movq	8(%rsi), %rcx
	sbbq	%r10, %rcx
	movq	%rcx, %r10
	movq	16(%rsi), %rdx
	sbbq	%r11, %rdx
	movq	%rdx, %r11
	movq	24(%rsi), %rsi
	sbbq	%rbp, %rsi
	movq	%rsi, %rbp
	movq	$6346243789798364141, %r8
	subq	%r8, %r9
	movq	$1503914060200516822, %r8
	sbbq	%r8, %r10
	movq	$0, %r8
	sbbq	%r8, %r11
	movq	$1152921504606846976, %r8
	sbbq	%r8, %rbp
	cmovnbq	%r9, %rax
	movq	%rax, %r9
	cmovnbq	%r10, %rcx
	movq	%rcx, %r10
	cmovnbq	%r11, %rdx
	movq	%rdx, %r11
	cmovnbq	%rbp, %rsi
	movq	%rsi, %rbp
	movq	$6346243789798364141, %r8
	subq	%r8, %r9
	movq	$1503914060200516822, %r8
	sbbq	%r8, %r10
	movq	$0, %r8
	sbbq	%r8, %r11
	movq	$1152921504606846976, %r8
	sbbq	%r8, %rbp
	cmovnbq	%r9, %rax
	cmovnbq	%r10, %rcx
	cmovnbq	%r11, %rdx
	cmovnbq	%rbp, %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	addq	$32, %rsp
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
