if exists("b:current_syntax")
    if b:current_syntax == 'verilog'
        syntax clear
    else
        finish
    endif
endif

let b:current_syntax = "systemverilog"

set commentstring=//%s
set synmaxcol=1000

"Syntax functions/commands {{{
    function! s:SynFunction(syn_type, group_name, list_to, link_to, ...)
        execute 'syntax '.a:syn_type.' '.a:group_name.' '.join(a:000, ' ')
        if a:list_to != 'NONE'
            execute 'syntax cluster '.a:list_to.' '.'add='.a:group_name
        endif
        if a:link_to != 'NONE'
            execute 'highlight default link '.a:group_name.' '.a:link_to
        endif
    endfunction

    command! -nargs=* Syn call s:SynFunction(<f-args>)

    function! s:SynMatchFunction(group_name, list_to, link_to, match_str, ...)
        execute 'syntax match '.a:group_name.' "'.{a:match_str}.'" '.join(a:000, ' ')
        if a:list_to != 'NONE'
            execute 'syntax cluster '.a:list_to.' '.'add='.a:group_name
        endif
        if a:link_to != 'NONE'
            execute 'highlight default link '.a:group_name.' '.a:link_to
        endif
    endfunction

    command! -nargs=* SynMatch call s:SynMatchFunction(<f-args>)
"}}}

"Misc {{{
    Syn region svAttribute NONE Comment
        \ start="(\*"
        \ end="\*)"
        \ contains=NONE
        \ keepend

    Syn match svOperator NONE NONE
        \ "[~!|&/*=<>+\^\-]"
        \ contains=NONE
        \ display

    " object.item[7].field
    " <-----><------>
    Syn match svParent NONE Type
        \ '\<\h\w*\%(\[\w*\]\)\?\.'
        \ contains=svDimension
        \ display

    "identifier (...) ::
    "identifier ::
    Syn match svStaticScope NONE Type
        \ "\<\h\w*\s*\%(#\s*(\_.\{-})\s*\)\?::"
        \ contains=svRParen
        \ containedin=svFunctionHeader,svTaskHeader
        \ display

    Syn match svFunctionCall NONE Function
        \ '\<\h\w*\ze\s*('
        \ contains=NONE
        \ nextgroup=svRParen
        \ skipwhite skipempty
        \ display

    Syn region svDimension svImplicitDataType Normal
        \ matchgroup=svParen
        \ start='\['
        \ end='\]'
        \ contains=@svCommon
        \ containedin=svPortList

    syntax region svUnpackedDimension
        \ matchgroup=svParen
        \ start='\['
        \ end='\]'
        \ contains=svNumber
        \ transparent

    syntax region svDataOrNetDeclaration
        \ start='\<\h\w*'
        \ end=';'me=s-1
        \ contains=svAssign,svNetType,svNonIntegerType,svIntegerAtomType,
        \svIntegerVectorType,svSigning,@svCommon
        \ transparent
        \ nextgroup=svEndStatement
        \ skipwhite skipempty

    Syn keyword svLifetime NONE Statement
        \ automatic static
        \ contained

    Syn keyword svClassItemQualifier NONE Statement
        \ static protected local
        \ contained

    Syn keyword svReturnWord NONE Keyword
        \ return
        \ contained containedin=svReturn

    Syn region svReturn NONE NONE
        \ start="\<return\>"
        \ end=";"
        \ contains=@svCommon,svReturnWord,svRParen
        \ contained
        \ containedin=@svSeqBodys

    "module_name # (params=0) u_instance ( .port(a) );
    "module_name              u_instance ( .port(a) );
    Syn match svModuleInstance NONE NONE
        \ "\<\h\w*\_s*\%(#\s*(\_.\{-})\_s*\)\?\<\h\w*\_s*(\_.\{-});"
        \ contains=svParamInstanceList
        \ containedin=@svStaticSeqBodys

    Syn match svVoidCast NONE svStatement
        \ "\<void'"
        \ containedin=@svSeqBodys
        \ nextgroup=svRParen
        \ skipwhite skipempty

    Syn keyword svVoid NONE svStatement
        \ void
        \ contained containedin=svFunctionHeader

    Syn region svPortInstanceList NONE NONE
        \ matchgroup=svOperator
        \ start="("
        \ end=")"
        \ contains=svPortInstanceName
        \ contained
        \ containedin=svModuleInstance

    Syn region svParamInstanceList NONE NONE
        \ matchgroup=svOperator
        \ start="#("
        \ end=")"
        \ contains=svPortInstanceName
        \ contained
        \ containedin=svModuleInstance

    Syn match svPortInstanceName NONE Special
        \ "\.\w\+"
        \ contained
        \ contains=NONE
        \ containedin=svPortInstanceList
        \ nextgroup=svRParen
        \ skipwhite skipempty

    Syn match svPortInstanceImplicit NONE Special
        \ "\.\*"
        \ contained
        \ contains=NONE
        \ containedin=svPortInstanceList

    Syn match svParamInstanceImplicit NONE Error
        \ "\.\*"
        \ contained
        \ contains=NONE
        \ containedin=svParamInstanceList

    syntax cluster svSeqBodys
        \ contains=svFunctionBody,svTaskBody,svSeqBlock,svCase,svDo

    syntax cluster svStaticSeqBodys
        \ contains=svModuleBody,svInterfaceBody,svStaticCase,svStaticSeqBlock,svGenerate

    Syn match svEndLabel NONE Label
        \ ":\_s*\w\+"hs=s+1
        \ contains=NONE

    Syn region svArgs NONE NONE
        \ matchgroup=svParen
        \ start="("
        \ end=")"
        \ contains=svArg
        \ contained

    Syn match svArg NONE NONE
        \ ".\{-}\ze[,)]"
        \ contained
        \ containedin=svArgs

    Syn region svParamAssign NONE NONE
        \ start="="
        \ end=";"
        \ contains=@svCommon,svOperator,svRParen,svUnpackedDimension
        \ contained
        \ transparent
        \ keepend

    Syn keyword svSigning svImplicitDataType Statement
        \ signed unsigned
        \ nextgroup=@svCommon,@svImplicitDataType
        \ skipwhite skipempty

    Syn region svPortList NONE NONE
        \ matchgroup=svOperator
        \ start="("
        \ end=")"
        \ contains=svAttribute,svPortDeclaration
        \ contained containedin=svModule,svModuleBody,svInterface,svInterfaceBody
        \ transparent

    Syn keyword svDefault NONE Keyword
        \ default
        \ contained

    Syn keyword svPortDeclaration NONE Type
        \ input output inout
        \ contained containedin=svPortList

    Syn keyword svNetType NONE Type
        \ supply0 supply1 tri triand trior trireg tri0 tri1 uwire wire wand wor
        \ containedin=svPortList
        \ nextgroup=@svImplicitDataType
        \ skipwhite skipempty

    Syn keyword svNonIntegerType NONE Type
        \ shortreal real realtime

    Syn keyword svIntegerAtomType NONE Type
        \ byte shortint int longint integer time
        \ containedin=svClassBody,svPackage,svProgram,@svStaticSeqBodys,
        \svFunctionBody,svTaskBody
        \ nextgroup=@svImplicitDataType
        \ skipwhite skipempty

    Syn keyword svIntegerVectorType NONE Type
        \ bit logic reg
        \ containedin=svPortList,svClassBody,svFunctionHeader,svFunctionBody,svTaskBody
        \ nextgroup=@svImplicitDataType
        \ skipwhite skipempty

    syntax cluster svDataType
        \ contains=
        \svIntegerAtomType,
        \svIntegerVectorType

    Syn region svStatement NONE NONE
        \ start='[^ ]'
        \ end=';'
        \ contains=svAssign
        \ contained containedin=NONE
        \ transparent
        \ keepend

    Syn match svEndStatement NONE svOperator
        \ ';'
        \ contains=NONE
        \ contained containedin=NONE

    Syn match svIdentifier NONE NONE
        \ '\<\h\w*\>'
        \ contains=NONE
        \ contained containedin=NONE

    Syn region svLocalParam NONE NONE
        \ matchgroup=svStatement
        \ start='localparam'
        \ end=';'he=s-1
        \ contains=@svImplicitDataType,svParamAssign
        \ containedin=@svStaticSeqBodys
        \ keepend

    Syn match svMethodName NONE Function
        \ '\w\+\ze\_s*\ze('
        \ contained
        \ nextgroup=svArgs
        \ skipwhite skipempty

    Syn region svDisable NONE NONE
        \ matchgroup=svStatement
        \ start='\<disable\>'
        \ end=';'he=s-1
        \ containedin=@svSeqBodys
        \ transparent
        \ keepend

    Syn keyword svVirtual NONE Statement
        \ virtual
        \ nextgroup=svClass,svFunction,svTask

    Syn match svIllegalIdentifier NONE Error
        \ "[^A-Za-z_ ]"
        \ contains=NONE
        \ contained
        \ containedin=svParam

    Syn keyword svInitial NONE svStatement
        \ initial
        \ containedin=@svStaticSeqBodys

    Syn keyword svFinal NONE svStatement
        \ final
        \ containedin=@svStaticSeqBodys
"}}}

"Regions {{{
    let s:sv_region_map_array = [
        \ {'name'            : 'svModule',
        \  'start'           : 'module'  ,
        \  'end'             : 'endmodule',
        \  'keepend'         : 0,
        \  'header_contains' : [
        \      'svImport',
        \      'svParamDeclList',
        \      'svPortList'
        \    ],
        \  'body_contains'   : [
        \      '@svAlways'              ,
        \      '@svCommon'              ,
        \      '@svConcurrentAssertions',
        \      'svCase'                 ,
        \      'svClass'                ,
        \      'svClocking'             ,
        \      'svDataOrNetDeclaration' ,
        \      'svDefaultDisableIff'    ,
        \      'svFunction'             ,
        \      'svGenerate'             ,
        \      'svInterface'            ,
        \      'svModule'               ,
        \      'svPortList'             ,
        \      'svRParen'               ,
        \      'svSeqBlock'             ,
        \      'svTask'
        \    ],
        \  'containedin'     : ['svModuleBody', 'svInterfaceBody']
        \ },
        \ {'name'            : 'svInterface',
        \  'start'           : 'interface'  ,
        \  'end'             : 'endinterface',
        \  'keepend'         : 0,
        \  'header_contains' : [
        \      'svImport',
        \      'svParamDeclList',
        \      'svPortList'
        \    ],
        \  'body_contains'   : [
        \      '@svAlways'             ,
        \      '@svCommon'             ,
        \      '@svConcurrentAssertions',
        \      'svCase'                ,
        \      'svClass'               ,
        \      'svClocking'            ,
        \      'svDataOrNetDeclaration',
        \      'svDefaultDisableIff'   ,
        \      'svFunction'            ,
        \      'svInterface'           ,
        \      'svModule'              ,
        \      'svPortList'            ,
        \      'svSeqBlock'            ,
        \      'svTask'
        \    ],
        \  'containedin'     : ['svModuleBody', 'svInterfaceBody']
        \ },
        \ {'name'            : 'svProgram',
        \  'start'           : 'program'  ,
        \  'end'             : 'endprogram',
        \  'keepend'         : 0,
        \  'header_contains' : ['svParamDeclList', 'svPortList'],
        \  'body_contains'   : [
        \      '@svCommon'        ,
        \      'svCase'           ,
        \      'svClass'          ,
        \      'svDataOrNetDeclaration',
        \      'svFunction'       ,
        \      'svGenerate'       ,
        \      'svRParen'         ,
        \      'svSeqBlock'       ,
        \      'svTask'
        \    ],
        \  'containedin'     : ['svProgramBody']
        \ },
        \ {'name'            : 'svFunction',
        \  'start'           : 'function'  ,
        \  'end'             : 'endfunction',
        \  'keepend'         : 1,
        \  'header_contains' : [
        \      'svLifetime',
        \      'svDimension',
        \      'svMethodName'
        \    ],
        \  'body_contains'   : [
        \      'svImmediateProperty',
        \      'svAssign',
        \      'svPortDeclaration',
        \      'svRParen',
        \      '@svCommon',
        \      'svSeqBlock',
        \      'svDo',
        \      'svCase'
        \    ],
        \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
        \ },
        \ {'name'            : 'svTask',
        \  'start'           : 'task'  ,
        \  'end'             : 'endtask',
        \  'keepend'         : 1,
        \  'header_contains' : [
        \      'svLifetime',
        \      'svMethodName'
        \    ],
        \  'body_contains'   : [
        \      'svImmediateProperty',
        \      'svAssign',
        \      'svPortDeclaration',
        \      'svRParen',
        \      '@svCommon',
        \      'svSeqBlock',
        \      'svDo'      ,
        \      'svCase'
        \    ],
        \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
        \ },
        \ {'name'            : 'svInterfaceClass',
        \  'start'           : 'interface\s\+class'  ,
        \  'end'             : 'endclass',
        \  'keepend'         : 0,
        \  'body_contains'   : ['svPureDecl'],
        \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
        \ },
        \ {'name'            : 'svClass',
        \  'start'           : 'class'  ,
        \  'end'             : 'endclass',
        \  'keepend'         : 0,
        \  'body_contains'   : [
        \      '@svCommon'           ,
        \      'svClass'             ,
        \      'svClassItemQualifier',
        \      'svConstraint'        ,
        \      'svExternDecl'        ,
        \      'svFunction'          ,
        \      'svLifetime'          ,
        \      'svPureDecl'          ,
        \      'svTask'              ,
        \      'svVirtual'
        \    ],
        \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
        \ },
        \ {'name'            : 'svProperty',
        \  'start'           : 'property'  ,
        \  'end'             : 'endproperty',
        \  'keepend'         : 1,
        \  'body_contains'   : ['NONE'],
        \  'containedin'     : ['svModuleBody', 'svInterfaceBody', 'svClassBody']
        \ },
        \ {'name'            : 'svSequence',
        \  'start'           : 'sequence'  ,
        \  'end'             : 'endsequence',
        \  'keepend'         : 1,
        \  'body_contains'   : ['NONE'],
        \  'containedin'     : ['svModuleBody', 'svInterfaceBody', 'svClassBody']
        \ },
        \ {'name'            : 'svCovergroup',
        \  'start'           : 'covergroup'  ,
        \  'end'             : 'endgroup',
        \  'keepend'         : 1,
        \  'body_contains'   : ['svCoverpointWord'],
        \  'containedin'     : ['svModuleBody', 'svInterfaceBody', 'svClassBody']
        \ },
        \ {'name'            : 'svClocking',
        \  'start'           : '\%(default\s\+\)\?clocking'  ,
        \  'end'             : 'endclocking',
        \  'keepend'         : 1,
        \  'header_contains' : ['svSensitivityList'],
        \  'body_contains'   : ['NONE'],
        \  'containedin'     : ['svModuleBody', 'svInterfaceBody']
        \ },
        \ {'name'            : 'svPackage',
        \  'start'           : 'package'  ,
        \  'end'             : 'endpackage',
        \  'keepend'         : 1,
        \  'body_contains'   : [
        \      'svClass'    ,
        \      'svFunction' ,
        \      'svInterface',
        \      'svModule'   ,
        \      'svTask'
        \    ]
        \ },
        \ {'name'            : 'svConfig',
        \  'start'           : 'config'  ,
        \  'end'             : 'endconfig',
        \  'keepend'         : 1,
        \  'body_contains'   : [
        \      'svDesignStatement',
        \      'svLocalParam',
        \      '@svConfigRuleStatement'
        \    ]
        \ }
        \ ]

    for sv_region in s:sv_region_map_array
        let s:region_cmd =
            \ 'syntax region ' . sv_region.name .
            \ ' matchgroup=svRegion'.
            \ ' start="\<' . sv_region.start . '\>"' .
            \ ' end="\<' . sv_region.end . '\>"' .
            \ ' contains=' . sv_region.name . 'Header,' . sv_region.name . 'Body' .
            \ ' nextgroup=svEndLabel skipwhite' .
            \ ' transparent'

        let s:region_header_cmd =
            \ 'syntax region '. sv_region.name .'Header' .
            \ ' start="."' .
            \ ' end=";"me=s-1'.
            \ ' nextgroup=' . sv_region.name . 'Body' .
            \ ' contained'

        let s:region_body_cmd =
            \ 'syntax region ' . sv_region.name . 'Body' .
            \ ' start=";"rs=e+1' .
            \ ' end="\<' . sv_region.end .'\>"me=s-1' .
            \ ' contains=' . join(sv_region.body_contains, ',') .
            \ ' contained' .
            \ ' containedin=' . sv_region.name .
            \ ' transparent'

        if has_key(sv_region, 'header_contains')
            let s:region_header_cmd .=
                \ ' contains=' . join(sv_region.header_contains, ',')
        endif

        if has_key(sv_region, 'containedin')
            let s:region_cmd .=
                \ ' containedin='.join(sv_region.containedin, ',')
        endif

        if sv_region.keepend
            let s:region_cmd      .= ' keepend'
            let s:region_body_cmd .= ' keepend'
        endif
        " let s:region_cmd .= ' fold'

        execute s:region_cmd
        execute s:region_header_cmd
        execute s:region_body_cmd
    endfor
"}}}

"Config {{{
    Syn region svDesignStatement NONE NONE
        \ matchgroup=svStatement
        \ start="\<design\>"
        \ end=";"me=s-1
        \ contained containedin=svConfig

    Syn keyword svDefaultLiblist svConfigRuleStatement Keyword
        \ default
        \ contained containedin=svConfig
        \ nextgroup=svLiblistClause
        \ skipwhite skipempty

    Syn region svInstClause svConfigRuleStatement NONE
        \ matchgroup=svStatement
        \ start="\<instance\>"
        \ end=";"me=s-1
        \ contains=svLiblistClause,svUseClause
        \ contained containedin=svConfig
        \ nextgroup=svIdentifier
        \ skipwhite skipempty

    Syn region svCellClause svConfigRuleStatement NONE
        \ matchgroup=svStatement
        \ start="\<cell\>"
        \ end=";"me=s-1
        \ contains=svLiblistClause,svUseClause
        \ contained containedin=svConfig
        \ nextgroup=svIdentifier
        \ skipwhite skipempty

    Syn keyword svLiblistClause svConfigRuleStatement svStatement
        \ liblist
        \ contained containedin=svInstClause,svCellClause
        \ nextgroup=svIdentifier
        \ skipwhite skipempty

    Syn keyword svUseClause svConfigRuleStatement svStatement
        \ use
        \ contained containedin=svInstClause,svCellClause
        \ nextgroup=svIdentifier
        \ skipwhite skipempty
"}}}

"Constants {{{
    let s:time_unit = '\%(s\|ms\|us\|ns\|ps\|fs\)'
    "let s:ZOrX = '[zZxX]'
    "let s:unbased_unsized_literal = "'[0-1]\|'".s:ZOrX
    let s:unbased_unsized_literal = "'[0-1zZxX]"
    let s:decimal_digit = "[0-9]"
    let s:unsigned_number = s:decimal_digit . '\%(_\|'. s:decimal_digit . '\)*'
    let s:time_literal = s:unsigned_number.'\s*'.s:time_unit

    SynMatch svTimeLiteral NONE Constant
        \ s:time_literal
        \ contains=NONE
        \ contained containedin=NONE

    SynMatch svUnbasedUnsizedLiteral NONE Constant
        \ s:unbased_unsized_literal
        \ contains=NONE
        \ contained containedin=NONE

    syntax cluster svConstantPrimary contains=
        \svRParen,
        \@svPrimaryLiteral,
        \svIdentifier

    syntax cluster svPrimaryLiteral contains=
        \svNumber,
        \svTimeLiteral,
        \svUnbasedUnsizedLiteral,
        \svStringLiteral
"}}}

"Delays {{{
    Syn match svCycleDelayRange NONE Special
        \ "##"
        \ containedin=svPropertyParen
        \ nextgroup=@svConstantPrimary,svCycleDelayConstRangeExpressionParen
        \ skipwhite skipempty

    Syn region svCycleDelayConstRangeExpressionParen NONE NONE
        \ matchgroup=svParen
        \ start="\["
        \ end="\]"
        \ contains=@svConstantPrimary
        \ contained containedin=NONE
"}}}

"Let {{{
    Syn region svLetDeclaration NONE NONE
        \ start="\<let\>"
        \ end=";"me=s-1
        \ contains=svLetWord
        \ nextgroup=svEndStatement
        \ containedin=@svStaticSeqBodys,svClassBody
        \ transparent

    Syn keyword svLetWord NONE Statement
        \ let
        \ nextgroup=svLetIdentifier
        \ skipwhite skipempty

    Syn match svLetIdentifier NONE NONE
        \ "\<\h\w*\>"
        \ contains=NONE
        \ contained
        \ containedin=NONE
        \ nextgroup=svLetPortList,svAssign
        \ skipwhite skipempty

    Syn region svLetPortList NONE NONE
        \ matchgroup=svParen
        \ start="("
        \ end=")"
        \ contains=NONE
        \ contained
        \ containedin=NONE
        \ nextgroup=svLetPortList,svAssign
        \ skipwhite skipempty
"}}}

"Parameters {{{
    "TODO: This section might be too strict.
    Syn region svParamDeclList NONE NONE
        \ matchgroup=svOperator
        \ start="#("
        \ end=")"
        \ contains=svParam
        \ contained containedin=svModule
        \ transparent
        \ nextgroup=svPortList skipwhite skipempty

    Syn match svParam NONE NONE
        \ "\h\_.\{-}\ze[,)]"
        \ contains=svParameterWord,svParamIdentifier,svIllegalIdentifier,svParamDefault
        \ contained
        \ containedin=svParamDeclList

    Syn keyword svParameterWord NONE svStatement
        \ parameter
        \ contained
        \ containedin=svParam
        \ nextgroup=svParamIdentifier,svIllegalIdentifier
        \ skipwhite skipempty

    Syn match svParamIdentifier NONE NONE
        \ "\<\h\w*\>"
        \ contains=NONE
        \ contained
        \ containedin=svParam
        \ nextgroup=svParamDefault
        \ skipwhite skipempty

    Syn match svParamDefault NONE NONE
        \ "=[^,)]*"
        \ contains=@svCommon
        \ contained
        \ containedin=NONE
"}}}

"Parenthesis {{{
    Syn region svRParen NONE Normal
        \ matchgroup=svParen
        \ start='('
        \ end=')'
        \ contains=@svCommon,@svConstantPrimary,svOperator,svTernary
        \ extend

    Syn region svConcat NONE Normal
        \ matchgroup=svParen
        \ start='{'
        \ end='}'
        \ contains=svConcat,@svConstantPrimary,svDimension,@svCommon

    Syn match svConcatDelimiter NONE svOperator
        \ ","
        \ contains=NONE
        \ containedin=svConcat
"}}}

"Import {{{
    Syn region svImport NONE NONE
        \ start="\<import\>"
        \ end=";"
        \ contains=svImportWord,svStaticScope
        \ nextgroup=svParamDeclList,svPortList
        \ skipwhite skipempty
        \ transparent
        \ keepend

    Syn keyword svImportWord NONE svStatement
        \ import
        \ contained
        \ containedin=svImport
"}}}

"Function/Task Declarations {{{
    Syn region svPureDecl NONE svStatement
        \ start="\<pure\%(\s\+virtual\)\>"
        \ end=";"he=s-1
        \ contains=svClassItemQualifier,svFunctionDecl,svTaskDecl

    Syn region svExternDecl NONE svStatement
        \ start="\<extern\>"
        \ end=";"he=s-1
        \ contains=svPureDecl,svClassItemQualifier,svModuleDecl,svFunctionDecl,svTaskDecl

    Syn region svModuleDecl NONE NONE
        \ matchgroup=svStatement
        \ start="\<module\>"
        \ end=";"me=s-1
        \ contains=svModuleHeader
        \ contained
        \ containedin=svExternDecl
        \ transparent

    Syn region svFunctionDecl NONE NONE
        \ matchgroup=svStatement
        \ start="\<function\>"
        \ end=";"me=s-1
        \ contains=svFunctionHeader
        \ contained
        \ containedin=svPureDecl,svExternDecl
        \ transparent

    Syn region svTaskDecl NONE NONE
        \ matchgroup=svStatement
        \ start="\<task\>"
        \ end=";"me=s-1
        \ contains=svTaskHeader
        \ contained
        \ containedin=svPureDecl,svExternDecl
        \ transparent
"}}}

"Generate {{{
    Syn region svGenerate svStaticSeqBodys NONE
        \ matchgroup=svRegion
        \ start="\<generate\>"
        \ end="\<endgenerate\>"
        \ contains=svStaticSeqBlock,@svAlways,svSensitivityList,svCond,@svConcurrentAssertions,svRParen
        \ containedin=svModuleBody,svInterfaceBody
        \ transparent
        \ keepend
"}}}

"Numbers {{{
    syntax match svNumber "\<[0-9]\+\>"                       display
    syntax match svNumber "[0-9]*'[sS]\?[bB][0-1_xX]\+"       display
    syntax match svNumber "[0-9]*'[sS]\?[oO][0-7_xX]\+"       display
    syntax match svNumber "[0-9]*'[sS]\?[dD][0-9_xX]\+"       display
    syntax match svNumber "[0-9]*'[sS]\?[hH][0-9a-fA-F_xX]\+" display

    highlight default link svNumber Number
"}}}

"Common {{{
    " Groups of syntax items that is used in most places.
    syntax cluster svCommon contains=
        \svConcat,
        \svCond,
        \svDimension,
        \svFunctionCall,
        \svNumber,
        \svParent,
        \svStaticScope,
        \svStringLiteral,
        \svSystemTask
"}}}

"Assignments {{{
    Syn region svAssignStatement NONE NONE
        \ matchgroup=svStatement
        \ start='assign'
        \ end=';'he=s-1
        \ contains=@svCommon,svAssign
        \ containedin=@svStaticSeqBodys
        \ transparent
        \ keepend
        \ nextgroup=svEndStatement
        \ skipwhite skipempty

    Syn region svAssign NONE NONE
        \ matchgroup=svOperator
        \ start='=\@<!<\?=\ze[^=]\?'
        \ end=';'me=s-1
        \ contains=@svCommon,svOperator,svRParen,svConditionalAssign,svTernary
        \ containedin=svAssignStatement
        \ transparent
        \ keepend

    Syn match svConditionalAssign NONE svOperator
        \ '?\|:'
        \ contains=NONE
        \ containedin=svAssign
        \ display

    Syn region svTernary NONE NONE
        \ matchgroup=svOperator
        \ start='?'
        \ end=';\|)'he=s-1
        \ contains=@svCommon,svTernary,svTernaryBranch,svOperator
        \ transparent
        \ keepend
        \ nextgroup=svEndStatement
        \ skipwhite skipempty

    Syn match svTernaryBranch NONE svOperator
        \ ':'
        \ contains=NONE
        \ containedin=svTernary
        \ display
"}}}

"Do Statements {{{
    Syn region svDo NONE NONE
        \ matchgroup=svConditional
        \ start='\<do\>'
        \ end='\<while\>.*;'he=s+4
        \ contains=svRParen,svDefault,svSeqBlock,svAssign
        \ transparent
"}}}

"Case Statements {{{
    "TODO: case () inside
    "TODO: case labels/blocks

    Syn region svCase NONE NONE
        \ matchgroup=svConditional
        \ start='\<case[zx]\?\>'
        \ end='\<endcase\>'
        \ contains=@svCommon,svCase,svDefault,svAssign,svReturn,
        \svFunctionCall

    Syn region svStaticCase svStaticSeqBodys NONE
        \ matchgroup=svConditional
        \ start='\<case[zx]\?\>'
        \ end='\<endcase\>'
        \ contains=@svCommon,svCase,svDefault,svAssign,
        \svFunctionCall

    Syn region svCaseParen NONE NONE
        \ matchgroup=svParen
        \ start='('
        \ end=')'
        \ contains=NONE
        \ contained containedin=svCase,svStaticCase
        \ transparent
        \ nextgroup=svInside
        \ skipwhite skipempty

    " Must be delcared after svCase
    Syn keyword svInside NONE Keyword
        \ inside
        \ contained
"}}}

"Sequential blocks (begin end) {{{
    Syn region svSeqBlock NONE NONE
        \ matchgroup=svRegion
        \ start="\<begin\>"
        \ end="\<end\>"
        \ contains=svAssign,svRParen,svSeqBlock,svCase,svDo,svDataOrNetDeclaration
        \ containedin=@svSeqBodys
        \ transparent
        \ nextgroup=svEndLabel
        \ skipwhite skipempty

    Syn region svStaticSeqBlock svStaticSeqBodys NONE
        \ matchgroup=svRegion
        \ start="\<begin\>"
        \ end="\<end\>"
        \ contains=svCase,svDataOrNetDeclaration,@svAlways,svAssign,svRParen,
        \svAssignStatement,svStaticSeqBlock,@svConcurrentAssertions,@svCommon
        \ containedin=@svStaticSeqBodys
        \ transparent
        \ nextgroup=svEndLabel
        \ skipwhite skipempty

    Syn match svSeqBlockLabel  NONE Label
        \ '\%(begin\s*:\s*\)\@<=\w\+'
        \ contained containedin=svSeqBlock,svStaticSeqBlock

    Syn match svError NONE Error
        \ "\s*\zs.*:\ze\s*end\>"
        \ contains=NONE
        \ containedin=svSeqBlock,svStaticSeqBlock
        \ display
"}}}

"Fork Statements {{{
    Syn region svFork NONE NONE
        \ matchgroup=svRegion
        \ start="\<fork\>"
        \ end="\<join\%(_all\|_none\)\?\>"
        \ contains=svSeqBlock,@svCommon
        \ containedin=@svSeqBodys
        \ transparent

    " Only procedural statements/blocks can be labelled.
    Syn match svError NONE Error
        \ "\s*\zs.*:\ze\s*join\%(_all\|_none\)\?\>"
        \ contains=NONE
        \ containedin=svFork
        \ display

    Syn match svWaitFork NONE svStatement
        \ '\<wait\_s\+fork\_s*;'he=e-1
        \ contains=none
        \ containedin=@svSeqBodys
"}}}

"Coverpoints {{{
    Syn keyword svCoverpointWord NONE svStatement
        \ coverpoint
        \ contained
        \ containedin=svCovergroupBody
        \ nextgroup=svCoverpointIdentifier
        \ skipwhite skipempty

    Syn match svCoverpointIdentifier NONE NONE
        \ "\<\h\w*\>"
        \ contains=NONE
        \ contained
        \ containedin=NONE
        \ nextgroup=svCoverpointBins
        \ skipwhite skipempty

    Syn region svCoverpointBins NONE NONE
        \ matchgroup=svParen
        \ start="{"
        \ end="}"
        \ contains=svCovergroupRangeList
        \ contained
        \ containedin=NONE

    Syn region svCovergroupRangeList NONE NONE
        \ matchgroup=svParen
        \ start="{"
        \ end="}"
        \ contains=NONE
        \ contained
        \ containedin=NONE
"}}}

"Typedef Statements {{{
    Syn keyword svStructWord NONE Typedef
        \ packed tagged
        \ containedin=svStruct

    Syn region svTypedef  NONE NONE
        \ matchgroup=svType
        \ start='\<typedef\>'
        \ end=';'me=s-1
        \ contains=svUnion,svStruct,svEnum
        \ containedin=svClassBody,svPackageBody,svProgramBody,@svStaticSeqBodys

    Syn region svUnion NONE NONE
        \ matchgroup=svType
        \ start='\<union\>'
        \ end=';'me=s-1
        \ containedin=svClassBody,svPackage,svProgram,@svStaticSeqBodys,
        \svFunctionBody,svTaskBody

    Syn region svStruct NONE NONE
        \ matchgroup=svType
        \ start='\<struct\>'
        \ end=';'me=s-1
        \ contains=svTypeParen,svStructWord
        \ containedin=svClassBody,svPackage,svProgram,@svStaticSeqBodys,
        \svFunctionBody,svTaskBody

    Syn region svEnum NONE NONE
        \ matchgroup=svType
        \ start='\<enum\>'
        \ end=';'me=s-1
        \ contains=svEnumParen,@svDataType,@svDimension
        \ containedin=svClassBody,svPackage,svProgram,@svStaticSeqBodys,
        \svFunctionBody,svTaskBody

    Syn region svTypeParen NONE NONE
        \ matchgroup=svParen
        \ start='{'
        \ end='}'
        \ contained containedin=svStruct
        \ contains=svDataOrNetDeclaration,svStruct,svUnion
        \ transparent

    Syn region svEnumParen NONE NONE
        \ matchgroup=svParen
        \ start='{'
        \ end='}'
        \ contained containedin=svEnum
        \ transparent
"}}}

"Conditionals {{{
    " lewis6991 (10th Nov 16): After a LOT of experimentation with the syntax
    " commands, I have come to the conclusion that it is impossible to define
    " regions for 'if' and 'else' statements that would be consistent and useful.
    " Therefore these statements will be treated independently to their conditional
    " blocks. It is feasible for other conditional blocks as they don't have an
    " 'else' but still quite difficult because comments can appear anywhere.
    Syn keyword svCond NONE Conditional
        \ if forever repeat while foreach
        \ containedin=@svSeqBodys,@svStaticSeqBodys
        \ nextgroup=svStatementError,svRParen
        \ skipwhite skipempty

    Syn keyword svFor NONE Conditional
        \ for
        \ containedin=@svSeqBodys
        \ nextgroup=svStatementError,svForParen
        \ skipwhite skipempty

    Syn region svForParen NONE NONE
        \ matchgroup=svParen
        \ start='('
        \ end=')'
        \ contains=@svDataType,svOperator,@svCommon
        \ contained
        \ containedin=NONE
        \ transparent

    Syn keyword svLoopGenerateConstruct NONE Conditional
        \ for
        \ containedin=@svStaticSeqBodys,svModuleBody,svInterfaceBody
        \ nextgroup=svStatementError,svLoopGenerateConstructParen
        \ skipwhite skipempty

    Syn region svLoopGenerateConstructParen NONE NONE
        \ matchgroup=svParen
        \ start='('
        \ end=')'
        \ contains=@svDataType,svOperator
        \ contained
        \ containedin=NONE
        \ transparent

    Syn keyword svGenvar NONE Type
        \ genvar
        \ containedin=svLoopGenerateConstructParen
        \ nextgroup=svIdentifier
        \ skipwhite skipempty

    Syn keyword svElse NONE Conditional
        \ else
        \ containedin=@svSeqBodys,@svStaticSeqBodys

    Syn match svStatementError NONE Error
        \ '[^( ]\+'
        \ contains=NONE
        \ contained
        \ containedin=NONE
        \ display
"}}}

"Always Statements {{{
    Syn keyword svAlwaysWord svAlways Statement
        \ always always_ff always_latch always_comb
        \ nextgroup=svAlwaysError2
        \ skipwhite skipempty

    Syn match svSensitivityList svAlways NONE
        \ "@\s*\*"
        \ display

    Syn region svSensitivityList NONE svOperator
        \ matchgroup=svParen
        \ start="@\_s*("
        \ end=")"
        \ contains=svSensitivityListWord
        \ transparent
        \ extend

    Syn keyword svSensitivityListWord NONE Statement
        \ posedge negedge or
        \ contained
        \ containedin=svSensitivityList

    " Only procedural statements/blocks can be labelled.
    Syn match svAlwaysError svAlways Error
        \ ".*:\ze\s*always\%(_ff\|_latch\|_comb\)\?\>"
        \ contains=NONE

    Syn match svAlwaysError2 NONE Error
        \ "\s*\zs:.*"
        \ contains=NONE
        \ contained containedin=NONE
"}}}

"Constraints {{{
    Syn region svConstraintBody NONE NONE
        \ start="{"
        \ end="}"me=s-1
        \ transparent
        \ contained
        \ containedin=svConstraint

    Syn region svConstraint NONE NONE
        \ matchgroup=svStatement
        \ start="constraint"
        \ end="}"he=s-1
        \ contains=svConstraintBody
        \ transparent
"}}}

"Assertions {{{
    Syn match svAssertLabel NONE Label
        \ "[a-zA-Z_][a-zA-Z_0-9]*\s*:\ze\_s*\%(assert\|assume\|cover\)\>"
        \ nextgroup=svConcurrentProperty skipwhite skipempty

    Syn keyword svAssertionKeyword NONE Statement
        \ assert assume cover property else
        \ contained
        \ containedin=svConcurrentProperty

    Syn region svConcurrentProperty NONE NONE
        \ start="\<\%(assert\|assume\|cover\)\s\+property\_s*("
        \ end=";"
        \ contains=svAssertionKeyword,svPropertyParen,svSystemTask
        \ transparent
        \ keepend

    Syn region svPropertyParen NONE NONE
        \ matchgroup=svParen
        \ start='('
        \ end=')'
        \ contains=@svCommon,svImplication,svSensitivityList,svDisableIff,svRParen
        \ contained
        \ containedin=svConcurrentProperty
        \ keepend
        \ transparent

    Syn region svImplication NONE NONE
        \ start='|[-=]>'
        \ end=');'me=s-1
        \ contained
        \ contains=@svCommon,svRParen,svOperator
        \ containedin=svPropertyParen
        \ transparent

    Syn cluster svConcurrentAssertions NONE NONE
        \ contains=svAssertLabel,svConcurrentProperty

    Syn region svImmediateProperty NONE NONE
        \ start="\<\%(assert\|assume\|cover\)\_s*("
        \ end=";"
        \ contains=svAssertionKeyword,svRParen
        \ transparent
"}}}

"Disable iff {{{
   Syn region svDefaultDisableIff NONE NONE
        \ matchgroup=svStatement
        \ start="\<\%(default\s*\)disable\s\+iff\s*\ze("
        \ end="\ze;"
        \ contains=svRParen
        \ containedin=svModuleBody,svInterface,svProperty,@svConcurrentAssertions
        \ keepend

    Syn match svDisableIff NONE svStatement
        \ "\<disable\_s\+iff\>"
        \ nextgroup=svRParen
        \ skipwhite skipempty
"}}}

"System Tasks {{{
    Syn match svSystemTask NONE Define
        \ "$\w\+\>"
        \ contains=NONE
        \ nextgroup=svSystemTaskParen
        \ display

    Syn region svSystemTaskParen NONE NONE
        \ matchgroup=svParen
        \ start="("
        \ end=")"
        \ contains=@svCommon,svRParen
        \ containedin=NONE
        \ transparent
        \ extend
"}}}

"Preprocessor {{{
    Syn match svPreproc NONE Define
        \ "`[a-zA-Z_][a-zA-Z_0-9]*"
        \ contains=NONE
        \ containedin=ALLBUT,@svContainsNone,@svDefines
        \ nextgroup=svPreprocParen
        "\ display "Cannot display

    Syn region svPreprocParen NONE NONE
        \ matchgroup=svParen
        \ start="("
        \ end=")"
        \ contains=@svCommon,svPreproc,svRParen
        \ contained containedin=NONE
        \ transparent
        \ keepend
        \ extend

    Syn match svPreprocParenArgDelim vDefines svOperator
        \ ","
        \ contained containedin=svPreprocParen

    Syn match svIfdef NONE Define
        \ "`\(ifn\?def\|elsif\|undef\)"
        \ contains=NONE
        \ containedin=ALLBUT,@svContainsNone
        \ nextgroup=svPreprocIdentifier
        \ skipwhite skipempty

    Syn match svPreprocIdentifier NONE Constant
        \ "\<\h\w*\>"
        \ contains=NONE
        \ contained
        \ containedin=NONE

    Syn match svInclude NONE NONE
        \ "`include\>"
        \ contains=NONE
        \ containedin=ALLBUT,@svContainsNone
        \ nextgroup=svStringLiteral
        \ skipwhite
        \ display
"}}}

"Defines {{{
    Syn match svDefineDeclaration svDefines Define
        \ "`define\>"
        \ contains=NONE
        \ containedin=svDefine
        \ nextgroup=svDefineIdentifier
        \ skipwhite skipempty

    Syn match svDefineIdentifier svDefines Constant
        \ "\h\w*"
        \ contains=NONE
        \ contained containedin=NONE
        \ nextgroup=svDefineArgs,svDefineBody
        \ skipwhite skipempty
        \ display

    Syn region svDefineBody svDefines NONE
        \ start="."
        \ skip="\\\\\n"
        \ end="\\n"
        \ contains=svDefineContinuation,svMacro
        \ contained containedin=NONE
        \ transparent
        \ keepend

    Syn region svDefine svDefines NONE
        \ start="`define\>"
        \ skip="\\\\\n"
        \ end="\\n"
        \ contains=svDefineDeclaration
        \ containedin=ALLBUT,@svContainsNone
        \ transparent
        \ keepend

    Syn match svDefineContinuation svDefines svOperator
        \ '\\\'
        \ contains=NONE
        \ contained containedin=svDefineBody

    Syn region svDefineArgs svDefines NONE
        \ matchgroup=svParen
        \ start="("
        \ end=")"
        \ contains=svDefineArgsDelimiter
        \ contained containedin=NONE
        \ transparent
        \ nextgroup=svDefineBody
        \ skipwhite skipempty
        \ display

    Syn match svDefineArgsDelimiter svDefines svOperator
        \ ","
        \ contains=NONE
        \ contained containedin=NONE
        \ display
"}}}

"String {{{
    Syn region svStringLiteral NONE String
        \ start=+"+
        \ skip=+\\\"+
        \ end=+"+
        \ contains=@Spell
        \ containedin=ALLBUT,@svContainsNone
        \ keepend
        \ extend
"}}}

"Comments {{{
    Syn region svComment NONE Comment
        \ start="/\*"
        \ end="\*/"
        \ contains=@Spell
        \ containedin=ALLBUT,@svContainsNone
        \ keepend
        \ extend

    Syn match svLineComment NONE Comment
        \ "//.*"
        \ contains=@Spell
        \ containedin=ALLBUT,@svContainsNone
        \ extend
"}}}

"Contains None Cluster {{{
    syntax cluster svContainsNone
        \ contains=
        \@svDefines,
        \svAttribute,
        \svComment,
        \svEndLabel,
        \svFunctionCall
        \svIfdef,
        \svLineComment,
        \svParent,
        \svPreproc,
        \svPreprocParen,
        \svStringLiteral,
        \svSystemTask,
        \svUndef,
"}}}

"Highlighting {{{
    highlight default link svConditional Conditional
    highlight default link svOperator    Special
    highlight default link svParen       Special
    highlight default link svRegion      Statement
    highlight default link svStatement   Statement
    highlight default link svType        Type
"}}}

"Syncing {{{
    " Only match on start of regions with no indent.
    syntax sync match svSync grouphere svModule    "^\<module\>"
    syntax sync match svSync grouphere svInterface "^\<interface\>"
    syntax sync match svSync grouphere svFunction  "^\<function\>"
    syntax sync match svSync grouphere svTask      "^\<task\>"
    syntax sync match svSync grouphere svClass     "^\<class\>"

    " If the end of a region has no indent, then assume it is at the top level and
    " hence is not contained in another syntax region. This massively speeds up
    " syntax highlighting of very large files.
    syntax sync match svSync grouphere NONE "^\<endfunction\>"
    syntax sync match svSync grouphere NONE "^\<endmodule\>"
    syntax sync match svSync grouphere NONE "^\<endinterface\>"
    syntax sync match svSync grouphere NONE "^\<endtask\>"
    syntax sync match svSync grouphere NONE "^\<endclass\>"
    syntax sync maxlines=50000
"}}}

" vim: foldmethod=marker:
