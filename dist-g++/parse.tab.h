typedef union {long itype; tree ttype; enum tree_code code; char *cptr; } YYSTYPE;

#ifndef YYLTYPE
typedef
  struct yyltype
 {
      int timestamp;
      int first_line;
      int first_column;
 int last_line;
      int last_column;
      char *text;
   }
 yyltype;

#define YYLTYPE yyltype
#endif

#define	YYACCEPT	return(0)
#define	YYABORT	return(1)
#define	YYERROR	return(1)
#define	IDENTIFIER	258
#define	TYPENAME	259
#define	SCSPEC	260
#define	TYPESPEC	261
#define	TYPE_QUAL	262
#define	CONSTANT	263
#define	STRING	264
#define	ELLIPSIS	265
#define	SIZEOF	266
#define	ENUM	267
#define	IF	268
#define	ELSE	269
#define	WHILE	270
#define	DO	271
#define	FOR	272
#define	SWITCH	273
#define	CASE	274
#define	DEFAULT	275
#define	BREAK	276
#define	CONTINUE	277
#define	RETURN	278
#define	GOTO	279
#define	ASM	280
#define	TYPEOF	281
#define	ALIGNOF	282
#define	AGGR	283
#define	DELETE	284
#define	NEW	285
#define	OVERLOAD	286
#define	PRIVATE	287
#define	PUBLIC	288
#define	PROTECTED	289
#define	THIS	290
#define	OPERATOR	291
#define	OPERATOR_PUSH	292
#define	OPERATOR_POP	293
#define	SCOPE	294
#define	EMPTY	295
#define	ASSIGN	296
#define	RANGE	297
#define	OROR	298
#define	ANDAND	299
#define	MIN_MAX	300
#define	EQCOMPARE	301
#define	ARITHCOMPARE	302
#define	LSHIFT	303
#define	RSHIFT	304
#define	UNARY	305
#define	PLUSPLUS	306
#define	MINUSMINUS	307
#define	HYPERUNARY	308
#define	POINTSAT	309
#define	TYPENAME_COLON	310
#define	TYPENAME_SCOPE	311
#define	TYPENAME_ELLIPSIS	312
#define	PRE_PARSED_FUNCTION_DECL	313

