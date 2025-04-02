function tlaHljs(hljs) {
    const n = {
        keyword: [
            'ACTION', 'ASSUME', 'ASSUMPTION', 'AXIOM', 'BY', 'CASE', 'CONSTANT',
            'CONSTANTS', 'DEF', 'DEFINE', 'DEFS', 'DOMAIN', 'ELSE', 'ENABLED',
            'EXCEPT', 'EXTENDS', 'HAVE', 'HIDE', 'IF', 'IN', 'INSTANCE', 'LAMBDA',
            'LEMMA', 'LET', 'LOCAL', 'MODULE', 'NEW', 'OBVIOUS', 'OMITTED', 'OTHER',
            'PICK', 'PROOF', 'PROPOSITION', 'PROOF', 'PROPOSITION', 'PROVE', 'QED',
            'RECURSIVE', 'STATE', 'SUBSET', 'SUFFICES', 'TAKE', 'TEMPORAL',
            'THEN', 'THEOREM', 'UNCHANGED', 'UNION', 'USE', 'VARIABLE', 'VARIABLES',
            'WITH', 'WITNESS'
        ],
        literal: [
            'FALSE', 'TRUE', 'BOOLEAN', 'STRING', 'Int', 'Nat', 'Real', 'Seq',
        ],
        punctuation: [',', '(', ')', '{', '}', '[', ']', ']_', '>>_'],
        // https://apalache-mc.org/docs/lang/standard-operators.html
        operator: [
            '/\\', '\\/', '<>', '=>', '<=>', '~>', '[]', '<>', 'ENABLED', 'UNCHANGED',
            '\\A', '\\E', '\\in', '\\notin', '\\subseteq', '\\union', '\\intersect',
            '\\X', '\\cdot', '\\oplus', '\\ominus', '\\otimes', '\\oslash',
            'WF_', 'SF_', '|->', '..', '^+', '^*', '^#', '^'
        ]
    };

    return {
        name: 'TLA+',
        case_insensitive: false,
        keywords: n,
        contains: [
            hljs.QUOTE_STRING_MODE,
            hljs.C_NUMBER_MODE,
            hljs.COMMENT('\\\\\\*', '$'),
            hljs.COMMENT('\\(\\*', '\\*\\)'),
        ],
    };
}

hljs.registerLanguage('tlaplus', tlaHljs);
hljs.registerLanguage('tla', tlaHljs);
hljs.highlightAll();

console.log("code hightlighted");