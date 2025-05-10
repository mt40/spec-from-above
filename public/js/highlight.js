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
            'WITH', 'WITNESS',
            // Cfg-specific keywords
            'SPECIFICATION', 'INVARIANT', 'PROPERTY', 'CONSTRAINT', 'SYMMETRY',
            'CONSTANT', 'CONSTANTS', 'INIT', 'NEXT', 'INITIALLY', 'ALWAYS',
            'EVENTUALLY', 'TEMPORAL', 'TEMPORALITY', 'TEMPORALITIES', 'CHECK_DEADLOCK', 'PROPERTIES'
        ],
        literal: [
            'FALSE', 'TRUE', 'BOOLEAN', 'STRING', 'Int', 'Nat', 'Real', 'Seq',
        ],
    };

    // https://apalache-mc.org/docs/lang/standard-operators.html
    const operators = [
        '==', '/\\\\', '\\\\/', '=>', '<=>', '~>', '[]', '<>',
        '\\\\A', '\\\\E', '\\\\in', '\\\\notin', '\\\\subseteq', '\\\\union', '\\\\intersect',
        'WF_', 'SF_', '\\|->', '<<', '>>', '\\[', '\\]', '{', '}', '\\(', '\\)', '!', '\\+', '\\*', '\\^#', '\\^'
    ];

    const operatorPatterns = operators.map(op => ({
        className: 'operator',
        begin: op,
        relevance: 0
    }));

    return {
        name: 'TLA+',
        case_insensitive: false,
        keywords: n,
        contains: [
            hljs.QUOTE_STRING_MODE,
            hljs.C_NUMBER_MODE,
            hljs.COMMENT('\\\\\\*', '$'),
            hljs.COMMENT('\\(\\*', '\\*\\)'),
            ...operatorPatterns
        ],
    };
}

hljs.registerLanguage('tlaplus', tlaHljs);
hljs.registerLanguage('tla', tlaHljs);
hljs.highlightAll();

console.log("code hightlighted");