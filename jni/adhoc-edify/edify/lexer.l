%{
/*
 * Copyright (C) 2009 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "expr.h"
#include "yydefs.h"
#include "parser.h"

int gLine = 1;
int gColumn = 1;
int gPos = 0;

// TODO: enforce MAX_STRING_LEN during lexing
char string_buffer[MAX_STRING_LEN];
char* string_pos;

#define ADVANCE do {yylloc.start=gPos; yylloc.end=gPos+yyleng; \
                    gColumn+=yyleng; gPos+=yyleng;} while(0)

%}

%x STR

%option noyywrap

%%


\" {
    BEGIN(STR);
    string_pos = string_buffer;
    yylloc.start = gPos;
    ++gColumn;
    ++gPos;
}

<STR>{
  \" {
      ++gColumn;
      ++gPos;
      BEGIN(INITIAL);
      *string_pos = '\0';
      yylval.str = strdup(string_buffer);
      yylloc.end = gPos;
      return STRING;
  }

  \\n   { gColumn += yyleng; gPos += yyleng; *string_pos++ = '\n'; }
  \\t   { gColumn += yyleng; gPos += yyleng;  *string_pos++ = '\t'; }
  \\\"  { gColumn += yyleng; gPos += yyleng;  *string_pos++ = '\"'; }
  \\\\  { gColumn += yyleng; gPos += yyleng;  *string_pos++ = '\\'; }

  \\x[0-9a-fA-F]{2} {
      gColumn += yyleng;
      gPos += yyleng;
      int val;
      sscanf(yytext+2, "%x", &val);
      *string_pos++ = val;
  }

  \r?\n {
      ++gLine;
      ++gPos;
      gColumn = 1;
      *string_pos++ = yytext[0];
  }
  
  \r {
      ++gLine;
      ++gPos;
      gColumn = 1;
      *string_pos++ = yytext[0];
  }
  

  . {
      ++gColumn;
      ++gPos;
      *string_pos++ = yytext[0];
  }
}

if                ADVANCE; return IF;
then              ADVANCE; return THEN;
else              ADVANCE; return ELSE;
endif             ADVANCE; return ENDIF;

[a-zA-Z0-9_:/.]+ {
  ADVANCE;
  yylval.str = strdup(yytext);
  return STRING;
}

\&\&              ADVANCE; return AND;
\|\|              ADVANCE; return OR;
==                ADVANCE; return EQ;
!=                ADVANCE; return NE;

[+(),!;]          ADVANCE; return yytext[0];

[ \t]+            ADVANCE;

(#.*)?\n          gPos += yyleng; ++gLine; gColumn = 1;

.                 return BAD;
