Caml1999N027����            -smyth/env.mli����  �  �  $  j�����1ocaml.ppx.context��&_none_@@ �A����������)tool_name���-ppxlib_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������/ppx_optcomp.env@�@@�������#env��&_none_A@ ��A@ �A��A@ ��A@ �A@@���-ocaml_version����'Defined��A@ ��A@ �A�������!4@��A@ ��A@ �A@@����"10@��#A@ ��$A@ �A@@����!0@��+A@ ��,A@ �A@@@��.A@ ��/A@ �A@@��1A@ ��2A@ �A@@@��4A@ ��5A@ �A@@@�@@�������@�@@@�@@�@@@@�@@@�@�ڠ����*ocaml.text���@@ ���@@ �A�������
  S Evaluation environments.

    This module provides functions that operate on the evaluation environment
    data structure used in {e Smyth}.

    Entries closer to the "beginning" of the environment shadow entries
    appearing later. Entries are typically "consed" to the beginning of an
    environment (for example, with {!add_res}). @��-smyth/env.mliA@@�H&X@@@@��A@@�H&X@@���@@ ���@@ �A��
A@@�H&X@������$Lang��JZ_�JZc@A��JZZ�JZc@@��JZZ�JZc@���Р%empty��#Lei�$Len@����#env��+Leq�,Let@@��.Leq�/Let@@@@���)ocaml.doc�� @@ ��!@@ �A�������	# The empty evaluation environment. @��@Muu�AMu�@@@@��CMuu�DMu�@@��1@@ ��2@@ �A@��ILee�JLet@��LLee�MLet@���Р'all_res��UO���VO��@��@����#env��_O���`O��@@��bO���cO��@@@����$list��jO���kO��@��������&string��vO���wO��@@��yO���zO��@@@�����#res���O����O��@@���O����O��@@@@���O����O��@@@@���O����O��@@@���O����O��@@@@���`��@@ ���@@ �A�������	� [all_res env] returns all name-to-{!Lang.res} bindings in the environment
    [env]; that is, the assignment of expression variables to results. @���P����Q_@@@@���P����Q_@@���@@ ���@@ �A@���O����O��@���O����O��@���Р(all_type���Sae��Sam@��@����#env���Sap��Sas@@���Sap��Sas@@@����$list���Sa���Sa�@��������&string���Sax��Sa~@@���Sax��Sa~@@@�����#typ���Sa���Sa�@@���Sa���Sa�@@@@���Sax��Sa�@@@@���Saw��Sa�@@@���Sap��Sa�@@@@�������@@ ���@@ �A�������	� [all_type env] returns all name-to-{!Lang.typ} bindings in the environment
    [env]; that is, the assignment of type variables to types. @���T����U�@@@@��T���U�@@���@@ ���@@ �A@��Saa�Sa�@��
Saa�Sa�@���Р&concat��W!�W'@��@����$list��W.�W2@�����#env��&W*�'W-@@��)W*�*W-@@@@��,W*�-W2@@@����#env��4W6�5W9@@��7W6�8W9@@@��:W*�;W9@@@@�����+@@ ��,@@ �A�������	& Concatenates a list of environments. @��KX::�LX:e@@@@��NX::�OX:e@@��<@@ ��=@@ �A@��TW�UW9@��WW�XW9@���Р'add_res��`Zgk�aZgr@��@�������&string��mZgu�nZg{@@��pZgu�qZg{@@@�����#res��yZg~�zZg�@@��|Zg~�}Zg�@@@@��Zgu��Zg�@@@��@����#env���Zg���Zg�@@���Zg���Zg�@@@����#env���Zg���Zg�@@���Zg���Zg�@@@���Zg���Zg�@@@���Zgu��Zg�@@@@���o���@@ ���@@ �A�������	H Adds a name-to-{!Lang.res} binding to the beginning of an environment. @���[����[��@@@@���[����[��@@���@@ ���@@ �A@���Zgg��Zg�@���Zgg��Zg�@���Р*concat_res���]����]��@��@����$list���]����]�@��������&string���]����]��@@���]����]��@@@�����#res���]����]��@@���]����]��@@@@���]����]��@@@@���]����]�@@@��@����#env���]���]�
@@���]���]�
@@@����#env��]��]�@@��]��]�@@@��	]��
]�@@@��]���]�@@@@���ް��@@ ���@@ �A�������	] Concatenates a list of name-to-{!Lang.res} bindings to the beginning of an
    environment. @��^�_at@@@@�� ^�!_at@@��@@ ��@@ �A@��&]���']�@��)]���*]�@���Р(add_type��2avz�3av�@��@�������&string��?av��@av�@@��Bav��Cav�@@@�����#typ��Kav��Lav�@@��Nav��Oav�@@@@��Qav��Rav�@@@��@����#env��[av��\av�@@��^av��_av�@@@����#env��fav��gav�@@��iav��jav�@@@��lav��mav�@@@��oav��pav�@@@@���A��`@@ ��a@@ �A�������	H Adds a name-to-{!Lang.typ} binding to the beginning of an environment. @���b����b��@@@@���b����b��@@��q@@ ��r@@ �A@���avv��av�@���avv��av�@���Р+concat_type���d����d��@��@����$list���d���d�@��������&string���d���d�@@���d���d�@@@�����#typ���d���d�@@���d���d�@@@@���d���d�@@@@���d���d�@@@��@����#env���d���d�@@���d���d�@@@����#env���d���d�"@@���d���d�"@@@���d���d�"@@@���d���d�"@@@@�������@@ ���@@ �A�������	] Concatenates a list of name-to-{!Lang.typ} bindings to the beginning of an
    environment. @���e##��fr�@@@@���e##��fr�@@���@@ ���@@ �A@���d����d�"@���d����d�"@@