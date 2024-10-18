Simplify:
     PAR_OPEN 'simplify' term+=Term+ smplKeywords=SimplifyKeyword* BValue* PAR_CLOSE;
    
terminal SimplifyKeyword:
  ':ite-extra-rules' | ':flat' | ':elim-and' | ':local-ctx' | ':local-ctx-limit' | ':blast-distinct' | ':som' | ':som-blowup' | 
  ':hoist-mul' | ':hoist-cmul' | ':algebraic-number-evaluator' | ':mul-to-power' | ':expand-power' | 
  ':expand-tan' | ':max-degree' | ':eq2ineq' | ':sort-sums' | ':gcd-rounding' | ':arith-lhs' | ':elim-to-real' | 
  ':push-to-real' | ':elim-rem' | ':udiv2mul' | ':split-concat-eq' | ':bit2bool' | ':blast-eq-value' | ':elim-sign-ext' | 
  ':hi-div0' | ':mul2concat' | ':expand-select-store' | ':sort-store' | ':max-memory' | ':max-steps' | ':push-ite-arith' | 
  ':push-ite-bv' | ':pull-cheap-ite' | ':cache-all';