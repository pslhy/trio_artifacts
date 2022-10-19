Caml1999N027����            /smyth/parse.mli����  "n  �    �����1ocaml.ppx.context��&_none_@@ �A����������)tool_name���-ppxlib_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������/ppx_optcomp.env@�@@�������#env��&_none_A@ ��A@ �A��A@ ��A@ �A@@���-ocaml_version����'Defined��A@ ��A@ �A�������!4@��A@ ��A@ �A@@����"10@��#A@ ��$A@ �A@@����!0@��+A@ ��,A@ �A@@@��.A@ ��/A@ �A@@��1A@ ��2A@ �A@@@��4A@ ��5A@ �A@@@�@@�������@�@@@�@@�@@@@�@@@�@�ڠ����*ocaml.text���@@ ���@@ �A�������	� Parsing of surface-level syntax.

    {b Note:} if there is a corresponding {!Post_parse} function to the function
    used for parsing here, it MUST be called afterward to ensure that the parsed
    value satisfies proper invariants. @��/smyth/parse.mliA@@�E � �@@@@��A@@�E � �@@���@@ ���@@ �A��
A@@�E � �@������$Lang��G � ��G � �@A��G � ��G � �@@��G � ��G � �@���A�    �'problem��$J %�%J ,@@@��Р2ExpectingLeftParen��,K/3�-K/E@�@@��0K/1�1K/E@@�Р3ExpectingRightParen��7LFJ�8LF]@�@@��;LFH�<LF]@@�Р4ExpectingLeftBracket��BM^b�CM^v@�@@��FM^`�GM^v@@�Р5ExpectingRightBracket��MNw{�NNw�@�@@��QNwy�RNw�@@�Р.ExpectingComma��XO���YO��@�@@��\O���]O��@@�Р3ExpectingRightArrow��cP���dP��@�@@��gP���hP��@@�Р/ExpectingLAngle��nQ���oQ��@�@@��rQ���sQ��@@�Р/ExpectingRAngle��yR���zR��@�@@��}R���~R��@@�Р.ExpectingSpace���S����S��@�@@���S����S��@@�Р.ExpectingPound���T����T�	@�@@���T����T�	@@�Р,ExpectingDot���U
��U
@�@@���U
��U
@@�Р/ExpectingEquals���V��V.@�@@���V��V.@@�Р5ExpectingDoubleEquals���W/3��W/H@�@@���W/1��W/H@@�Р-ExpectingHole���XIM��XIZ@�@@���XIK��XIZ@@�Р/ExpectingLambda���Y[_��Y[n@�@@���Y[]��Y[n@@�Р-ExpectingPipe���Zos��Zo�@�@@���Zoq��Zo�@@�Р.ExpectingColon���[����[��@�@@���[����[��@@�Р1ExpectingFuncSpec���\����\��@�@@���\����\��@@�Р1ExpectingWildcard���^����^��@�@@���^����^��@@�Р4ExpectingLineComment���_����_��@�@@��_���_��@@�Р:ExpectingMultiCommentStart��`���	`��@�@@��`���`��@@�Р8ExpectingMultiCommentEnd��a���a�@�@@��a���a�@@�Р0ExpectingExactly��c�c+@������#int��(c/�)c2@@��+c/�,c2@@@�����#int��4c5�5c8@@��7c5�8c8@@@@@��:c�;c8@@�Р3ExpectingMoreIndent��Ae:>�Be:Q@�@@��Ee:<�Fe:Q@@�Р,ExpectingLet��LgSW�MgSc@�@@��PgSU�QgSc@@�Р+ExpectingIn��Whdh�Xhds@�@@��[hdf�\hds@@�Р-ExpectingCase��bitx�cit�@�@@��fitv�git�@@�Р+ExpectingOf��mj���nj��@�@@��qj���rj��@@�Р-ExpectingType��xk���yk��@�@@��|k���}k��@@�Р/ExpectingAssert���l����l��@�@@���l����l��@@�Р,ExpectingNat���n����n��@�@@���n����n��@@�Р8ExpectingConstructorName���p����p��@�@@���p����p��@@�Р5ExpectingVariableName���q����q�@�@@���q����q�@@�Р1ExpectingHoleName���r
��r@�@@���r��r@@�Р6ExpectingFunctionArity���t!��t7@�@@���t��t7@@�Р2ExpectingTupleSize���v9=��v9O@�@@���v9;��v9O@@�Р3ExpectingTupleIndex���wPT��wPg@�@@���wPR��wPg@@�Р-ExpectingName���yim��yiz@������&string���yi~��yi�@@���yi~��yi�@@@�����&string���yi���yi�@@���yi���yi�@@@@@���yik��yi�@@�Р-NegativeArity���{����{��@������#int��{���	{��@@��{���{��@@@@@��{���{��@@�Р)ZeroArity��|���|��@�@@��|���|��@@�Р,ExpectingEnd�� ~���!~��@�@@��$~���%~��@@@A@���)ocaml.doc��@@ ��@@ �A�������< The possible parse errors. @��6I � ��7I �@@@@��9I � ��:I �@@��'@@ ��(@@ �A@��?J  �@~��@@��BJ  �C~��@���A�    �'context��L A���M A��@@@��Р%CType��T B� �U B�@�@@��X B���Y B�@@�Р'CTTuple��_ C
�` C@�@@��c C�d C@@�Р&CTData��j D�k D@�@@��n D�o D@@�Р%CTArr��u E!�v E&@�@@��y E�z E&@@�Р(CTForall��� F'+�� F'3@�@@��� F')�� F'3@@�Р%CTVar��� G48�� G4=@�@@��� G46�� G4=@@�Р*CTypeParam��� I?C�� I?M@�@@��� I?A�� I?M@@�Р(CTypeArg��� JNR�� JNZ@�@@��� JNP�� JNZ@@�Р$CPat��� L\`�� L\d@�@@��� L\^�� L\d@@�Р'CPTuple��� Mei�� Mep@�@@��� Meg�� Mep@@�Р%CPVar��� Nqu�� Nqz@�@@��� Nqs�� Nqz@@�Р*CPWildcard��� O{�� O{�@�@@��� O{}�� O{�@@�Р$CExp��� Q���� Q��@�@@��� Q���� Q��@@�Р%CELet��� R���� R��@�@@��� R���� R��@@�Р%CEVar��� S���� S��@�@@��� S���� S��@@�Р&CECtor��� T���� T��@�@@��� T���� T��@@�Р'CETuple�� U��� U��@�@@�� U���	 U��@@�Р&CEProj�� V��� V��@�@@�� V��� V��@@�Р%CEApp�� W��� W��@�@@�� W��� W��@@�Р&CEHole��% X���& X��@�@@��) X���* X��@@�Р(CELambda��0 Y���1 Y��@�@@��4 Y���5 Y��@@�Р&CECase��; Z���< Z��@�@@��? Z���@ Z��@@�Р&CEList��F [���G [�@�@@��J [���K [�@@�Р%CENat��Q \�R \@�@@��U \�V \@@�Р*CStatement��\ ^�] ^@�@@��` ^�a ^@@�Р*CSDatatype��g _ �h _*@�@@��k _�l _*@@�Р/CSDatatypeCtors��r `+/�s `+>@�@@��v `+-�w `+>@@�Р,CSDefinition��} a?C�~ a?O@�@@��� a?A�� a?O@@�Р+CSAssertion��� bPT�� bP_@�@@��� bPR�� bP_@@�Р*CSFuncSpec��� c`d�� c`n@�@@��� c`b�� c`n@@�Р/CSFuncSpecInput��� dos�� do�@�@@��� doq�� do�@@�Р0CSFuncSpecOutput��� e���� e��@�@@��� e���� e��@@�Р(CProgram��� g���� g��@�@@��� g���� g��@@@A@�������@@ ���@@ �A�������> The possible parse contexts. @��� @���� @��@@@@��� @���� @��@@���@@ ���@@ �A@��� A���� g��@@��� A���� g��@���A�    �&parser��� j���� j��@����!a��� j���� j��@@@B@@@A������$Bark&parser��� k���� k��@�����'context��� k���� k��@@��� k���� k��@@@�����'problem�� k��� k��@@��
 k��� k��@@@���!a�� k��� k��@@@@�� k��� k��@@@�����@@ ��@@ �A�������7 The type of a parser. @��% i���& i��@@@@��( i���) i��@@��@@ ��@@ �A@��. j���/ k��@@��1 j���2 k��@���Р#exp��: n�; n@����&parser��B n#�C n)@�����#exp��K n�L n"@@��N n�O n"@@@@��Q n�R n)@@@@���-��B@@ ��C@@ �A�������4 Expression parser. @��b m���c m�@@@@��e m���f m�@@��S@@ ��T@@ �A@��k n�l n)@��n n�o n)@���Р#typ��w q?C�x q?F@����&parser�� q?M�� q?S@�����#typ��� q?I�� q?L@@��� q?I�� q?L@@@@��� q?I�� q?S@@@@���j��@@ ���@@ �A�������. Type parser. @��� p++�� p+>@@@@��� p++�� p+>@@���@@ ���@@ �A@��� q??�� q?S@��� q??�� q?S@���Р'program��� w���� w��@����&parser��� w���� w��@������'Desugar'program��� w���� w��@@��� w���� w��@@@@��� w���� w��@@@@�������@@ ���@@ �A�������	 Program parser.

    {b Warning:} parses expressions but does NOT call {!Post_parse.exp}
    (happens in {!Desugar.program}). @��� sUU�� v��@@@@��� sUU�� v��@@���@@ ���@@ �A@��� w���� w��@��� w���� w��@@