import PlattAssemblyKernel
import PlattCertificates.Count131072.C012720
import PlattCertificates.Count131072.C012721
import PlattCertificates.Count131072.C012722
import PlattCertificates.Count131072.C012723
import PlattCertificates.Count131072.C012724
import PlattCertificates.Count131072.C012725
import PlattCertificates.Count131072.C012726
import PlattCertificates.Count131072.C012727
import PlattCertificates.Count131072.C012728
import PlattCertificates.Count131072.C012729
import PlattCertificates.Count131072.C012730
import PlattCertificates.Count131072.C012731
import PlattCertificates.Count131072.C012732
import PlattCertificates.Count131072.C012733
import PlattCertificates.Count131072.C012734
import PlattCertificates.Count131072.C012735
import PlattCertificates.Count131072.C012736
import PlattCertificates.Count131072.C012737
import PlattCertificates.Count131072.C012738
import PlattCertificates.Count131072.C012739
import PlattCertificates.Count131072.C012740
import PlattCertificates.Count131072.C012741
import PlattCertificates.Count131072.C012742
import PlattCertificates.Count131072.C012743
import PlattCertificates.Count131072.C012744
import PlattCertificates.Count131072.C012745
import PlattCertificates.Count131072.C012746
import PlattCertificates.Count131072.C012747
import PlattCertificates.Count131072.C012748
import PlattCertificates.Count131072.C012749
import PlattCertificates.Count131072.C012750
import PlattCertificates.Count131072.C012751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12720 : List PrefixCut := [⟨15,118068899,118068988⟩,
⟨66,529870129,529870526⟩,
⟨118,963889806,963890522⟩,
⟨128,1045235390,1045236166⟩]
theorem checked12720 : checkPrefixCuts (2^48) 1671168001 9 Manual.Count131072.C012720.packed 128 cuts12720 = true := by
 decide +kernel
def pointBounds12720 : List (Nat × Nat × Nat) := [(1671183360,94096830748585,94097207263412),(1671235584,94097242549815,94097619064950),(1671288832,94097676569492,94098053084946)]
theorem point_links_checked12720 : (cuts12720.take 3).map (fun c => (1671168001-1+2*2^9*c.k,94096712679686+c.lower,94097089194424+c.upper)) = pointBounds12720 := by
 decide +kernel
def cuts12721 : List PrefixCut := [⟨42,336492497,336492742⟩,
⟨94,758022243,758022798⟩,
⟨128,1036227889,1036228646⟩]
theorem checked12721 : checkPrefixCuts (2^48) 1671299073 9 Manual.Count131072.C012721.packed 128 cuts12721 = true := by
 decide +kernel
def pointBounds12721 : List (Nat × Nat × Nat) := [(1671342080,94098094407573,94098470923332),(1671395328,94098515937319,94098892453388)]
theorem point_links_checked12721 : (cuts12721.take 2).map (fun c => (1671299073-1+2*2^9*c.k,94097757915076+c.lower,94098134430590+c.upper)) = pointBounds12721 := by
 decide +kernel
def cuts12722 : List PrefixCut := [⟨18,148194374,148194482⟩,
⟨70,569192105,569192521⟩,
⟨122,993376002,993376728⟩,
⟨128,1040188625,1040189386⟩]
theorem checked12722 : checkPrefixCuts (2^48) 1671430145 9 Manual.Count131072.C012722.packed 128 cuts12722 = true := by
 decide +kernel
def pointBounds12722 : List (Nat × Nat × Nat) := [(1671448576,94098942337339,94099318853718),(1671501824,94099363335070,94099739851757),(1671555072,94099787518967,94100164035964)]
theorem point_links_checked12722 : (cuts12722.take 3).map (fun c => (1671430145-1+2*2^9*c.k,94098794142965+c.lower,94099170659236+c.upper)) = pointBounds12722 := by
 decide +kernel
def cuts12723 : List PrefixCut := [⟨46,377189189,377189465⟩,
⟨98,804376913,804377496⟩,
⟨128,1047515801,1047516562⟩]
theorem checked12723 : checkPrefixCuts (2^48) 1671561217 9 Manual.Count131072.C012723.packed 128 cuts12723 = true := by
 decide +kernel
def pointBounds12723 : List (Nat × Nat × Nat) := [(1671608320,94100211520779,94100588038087),(1671661568,94100638708503,94101015226118)]
theorem point_links_checked12723 : (cuts12723.take 2).map (fun c => (1671561217-1+2*2^9*c.k,94099834331590+c.lower,94100210848622+c.upper)) = pointBounds12723 := by
 decide +kernel
def cuts12724 : List PrefixCut := [⟨22,176458094,176458227⟩,
⟨74,599409207,599409651⟩,
⟨126,1018305965,1018306720⟩,
⟨128,1032280186,1032280951⟩]
theorem checked12724 : checkPrefixCuts (2^48) 1671692289 9 Manual.Count131072.C012724.packed 128 cuts12724 = true := by
 decide +kernel
def pointBounds12724 : List (Nat × Nat × Nat) := [(1671714816,94101058305485,94101434823411),(1671768064,94101481256598,94101857774835),(1671821312,94101900153356,94102276671904)]
theorem point_links_checked12724 : (cuts12724.take 3).map (fun c => (1671692289-1+2*2^9*c.k,94100881847391+c.lower,94101258365184+c.upper)) = pointBounds12724 := by
 decide +kernel
def cuts12725 : List PrefixCut := [⟨50,405077614,405077911⟩,
⟨102,826136417,826137022⟩,
⟨128,1047182783,1047183547⟩]
theorem checked12725 : checkPrefixCuts (2^48) 1671823361 9 Manual.Count131072.C012725.packed 128 cuts12725 = true := by
 decide +kernel
def pointBounds12725 : List (Nat × Nat × Nat) := [(1671874560,94102319205191,94102695724046),(1671927808,94102740263994,94103116783157)]
theorem point_links_checked12725 : (cuts12725.take 2).map (fun c => (1671823361-1+2*2^9*c.k,94101914127577+c.lower,94102290646135+c.upper)) = pointBounds12725 := by
 decide +kernel
def cuts12726 : List PrefixCut := [⟨26,215150599,215150756⟩,
⟨78,640391159,640391628⟩,
⟨128,1042050821,1042051587⟩]
theorem checked12726 : checkPrefixCuts (2^48) 1671954433 9 Manual.Count131072.C012726.packed 128 cuts12726 = true := by
 decide +kernel
def pointBounds12726 : List (Nat × Nat × Nat) := [(1671981056,94103176460959,94103552980438),(1672034304,94103601701519,94103978221310)]
theorem point_links_checked12726 : (cuts12726.take 2).map (fun c => (1671954433-1+2*2^9*c.k,94102961310360+c.lower,94103337829682+c.upper)) = pointBounds12726 := by
 decide +kernel
def cuts12727 : List PrefixCut := [⟨2,15655388,15655400⟩,
⟨54,434640573,434640895⟩,
⟨106,866237033,866237671⟩,
⟨128,1045167106,1045167873⟩]
theorem checked12727 : checkPrefixCuts (2^48) 1672085505 9 Manual.Count131072.C012727.packed 128 cuts12727 = true := by
 decide +kernel
def pointBounds12727 : List (Nat × Nat × Nat) := [(1672087552,94104019016569,94104395536669),(1672140800,94104438001754,94104814522164),(1672194048,94104869598214,94105246118940)]
theorem point_links_checked12727 : (cuts12727.take 3).map (fun c => (1672085505-1+2*2^9*c.k,94104003361181+c.lower,94104379881269+c.upper)) = pointBounds12727 := by
 decide +kernel
def cuts12728 : List PrefixCut := [⟨30,237840193,237840369⟩,
⟨82,660488208,660488690⟩,
⟨128,1037174056,1037174815⟩]
theorem checked12728 : checkPrefixCuts (2^48) 1672216577 9 Manual.Count131072.C012728.packed 128 cuts12728 = true := by
 decide +kernel
def pointBounds12728 : List (Nat × Nat × Nat) := [(1672247296,94105286368480,94105662889511),(1672300544,94105709016495,94106085537832)]
theorem point_links_checked12728 : (cuts12728.take 2).map (fun c => (1672216577-1+2*2^9*c.k,94105048528287+c.lower,94105425049142+c.upper)) = pointBounds12728 := by
 decide +kernel
def cuts12729 : List PrefixCut := [⟨6,48810168,48810202⟩,
⟨58,474965831,474966177⟩,
⟨110,905820418,905821080⟩,
⟨128,1051398998,1051399767⟩]
theorem checked12729 : checkPrefixCuts (2^48) 1672347649 9 Manual.Count131072.C012729.packed 128 cuts12729 = true := by
 decide +kernel
def pointBounds12729 : List (Nat × Nat × Nat) := [(1672353792,94106134512511,94106511034159),(1672407040,94106560668174,94106937190134),(1672460288,94106991522761,94107368045037)]
theorem point_links_checked12729 : (cuts12729.take 3).map (fun c => (1672347649-1+2*2^9*c.k,94106085702343+c.lower,94106462223957+c.upper)) = pointBounds12729 := by
 decide +kernel
def cuts12730 : List PrefixCut := [⟨34,281559661,281559870⟩,
⟨86,690845365,690845873⟩,
⟨128,1033309384,1033310140⟩]
theorem checked12730 : checkPrefixCuts (2^48) 1672478721 9 Manual.Count131072.C012730.packed 128 cuts12730 = true := by
 decide +kernel
def pointBounds12730 : List (Nat × Nat × Nat) := [(1672513536,94107418661002,94107795183594),(1672566784,94107827946706,94108204469597)]
theorem point_links_checked12730 : (cuts12730.take 2).map (fun c => (1672478721-1+2*2^9*c.k,94107137101341+c.lower,94107513623724+c.upper)) = pointBounds12730 := by
 decide +kernel
def cuts12731 : List PrefixCut := [⟨10,78083914,78083974⟩,
⟨62,494411456,494411824⟩,
⟨114,930582320,930583008⟩,
⟨128,1038108361,1038109129⟩]
theorem checked12731 : checkPrefixCuts (2^48) 1672609793 9 Manual.Count131072.C012731.packed 128 cuts12731 = true := by
 decide +kernel
def pointBounds12731 : List (Nat × Nat × Nat) := [(1672620032,94108248494639,94108625017838),(1672673280,94108664822181,94109041345688),(1672726528,94109100993045,94109477516872)]
theorem point_links_checked12731 : (cuts12731.take 3).map (fun c => (1672609793-1+2*2^9*c.k,94108170410725+c.lower,94108546933864+c.upper)) = pointBounds12731 := by
 decide +kernel
def cuts12732 : List PrefixCut := [⟨38,308438320,308438548⟩,
⟨90,736168189,736168732⟩,
⟨128,1045262635,1045263407⟩]
theorem checked12732 : checkPrefixCuts (2^48) 1672740865 9 Manual.Count131072.C012732.packed 128 cuts12732 = true := by
 decide +kernel
def pointBounds12732 : List (Nat × Nat × Nat) := [(1672779776,94109516957406,94109893481541),(1672833024,94109944687275,94110321211725)]
theorem point_links_checked12732 : (cuts12732.take 2).map (fun c => (1672740865-1+2*2^9*c.k,94109208519086+c.lower,94109585042993+c.upper)) = pointBounds12732 := by
 decide +kernel
def cuts12733 : List PrefixCut := [⟨14,114751783,114751867⟩,
⟨66,533032111,533032506⟩,
⟨118,950962570,950963268⟩,
⟨128,1033403014,1033403771⟩]
theorem checked12733 : checkPrefixCuts (2^48) 1672871937 9 Manual.Count131072.C012733.packed 128 cuts12733 = true := by
 decide +kernel
def pointBounds12733 : List (Nat × Nat × Nat) := [(1672886272,94110368533504,94110745058267),(1672939520,94110786813832,94111163338906),(1672992768,94111204744291,94111581269668)]
theorem point_links_checked12733 : (cuts12733.take 3).map (fun c => (1672871937-1+2*2^9*c.k,94110253781721+c.lower,94110630306400+c.upper)) = pointBounds12733 := by
 decide +kernel
def cuts12734 : List PrefixCut := [⟨42,331270780,331271024⟩,
⟨94,758427807,758428363⟩,
⟨128,1034667826,1034668582⟩]
theorem checked12734 : checkPrefixCuts (2^48) 1673003009 9 Manual.Count131072.C012734.packed 128 cuts12734 = true := by
 decide +kernel
def pointBounds12734 : List (Nat × Nat × Nat) := [(1673046016,94111618455515,94111994981195),(1673099264,94112045612542,94112422138534)]
theorem point_links_checked12734 : (cuts12734.take 2).map (fun c => (1673003009-1+2*2^9*c.k,94111287184735+c.lower,94111663710171+c.upper)) = pointBounds12734 := by
 decide +kernel
def cuts12735 : List PrefixCut := [⟨18,144005899,144006006⟩,
⟨70,559696223,559696638⟩,
⟨122,980083592,980084320⟩,
⟨128,1025671006,1025671769⟩]
theorem checked12735 : checkPrefixCuts (2^48) 1673134081 9 Manual.Count131072.C012735.packed 128 cuts12735 = true := by
 decide +kernel
def pointBounds12735 : List (Nat × Nat × Nat) := [(1673152512,94112465858460,94112842384759),(1673205760,94112881548784,94113258075391),(1673259008,94113301936153,94113678463073)]
theorem point_links_checked12735 : (cuts12735.take 3).map (fun c => (1673134081-1+2*2^9*c.k,94112321852561+c.lower,94112698378753+c.upper)) = pointBounds12735 := by
 decide +kernel
def cuts12736 : List PrefixCut := [⟨46,368057922,368058197⟩,
⟨98,785727160,785727739⟩,
⟨128,1026431848,1026432601⟩]
theorem checked12736 : checkPrefixCuts (2^48) 1673265153 9 Manual.Count131072.C012736.packed 128 cuts12736 = true := by
 decide +kernel
def pointBounds12736 : List (Nat × Nat × Nat) := [(1673312256,94113715581489,94114092108719),(1673365504,94114133250727,94114509778261)]
theorem point_links_checked12736 : (cuts12736.take 2).map (fun c => (1673265153-1+2*2^9*c.k,94113347523567+c.lower,94113724050522+c.upper)) = pointBounds12736 := by
 decide +kernel
def cuts12737 : List PrefixCut := [⟨22,173923568,173923697⟩,
⟨74,598126061,598126498⟩,
⟨126,1020464902,1020465648⟩,
⟨128,1036611399,1036612158⟩]
theorem checked12737 : checkPrefixCuts (2^48) 1673396225 9 Manual.Count131072.C012737.packed 128 cuts12737 = true := by
 decide +kernel
def pointBounds12737 : List (Nat × Nat × Nat) := [(1673418752,94114547878983,94114924406820),(1673472000,94114972081476,94115348609621),(1673525248,94115394420317,94115770948771)]
theorem point_links_checked12737 : (cuts12737.take 3).map (fun c => (1673396225-1+2*2^9*c.k,94114373955415+c.lower,94114750483123+c.upper)) = pointBounds12737 := by
 decide +kernel
def cuts12738 : List PrefixCut := [⟨50,402815046,402815341⟩,
⟨102,827481538,827482147⟩,
⟨128,1039389289,1039390054⟩]
theorem checked12738 : checkPrefixCuts (2^48) 1673527297 9 Manual.Count131072.C012738.packed 128 cuts12738 = true := by
 decide +kernel
def pointBounds12738 : List (Nat × Nat × Nat) := [(1673578496,94115813381860,94116189910622),(1673631744,94116238048352,94116614577428)]
theorem point_links_checked12738 : (cuts12738.take 2).map (fun c => (1673527297-1+2*2^9*c.k,94115410566814+c.lower,94115787095281+c.upper)) = pointBounds12738 := by
 decide +kernel
def cuts12739 : List PrefixCut := [⟨26,205513567,205513722⟩,
⟨78,630321225,630321693⟩,
⟨128,1029722161,1029722921⟩]
theorem checked12739 : checkPrefixCuts (2^48) 1673658369 9 Manual.Count131072.C012739.packed 128 cuts12739 = true := by
 decide +kernel
def pointBounds12739 : List (Nat × Nat × Nat) := [(1673684992,94116655469670,94117031999057),(1673738240,94117080277328,94117456807028)]
theorem point_links_checked12739 : (cuts12739.take 2).map (fun c => (1673658369-1+2*2^9*c.k,94116449956103+c.lower,94116826485335+c.upper)) = pointBounds12739 := by
 decide +kernel
def cuts12740 : List PrefixCut := [⟨2,17489279,17489292⟩,
⟨54,435543372,435543691⟩,
⟨106,854424895,854425521⟩,
⟨128,1036031431,1036032187⟩]
theorem checked12740 : checkPrefixCuts (2^48) 1673789441 9 Manual.Count131072.C012740.packed 128 cuts12740 = true := by
 decide +kernel
def pointBounds12740 : List (Nat × Nat × Nat) := [(1673791488,94117497167543,94117873697548),(1673844736,94117915221636,94118291751947),(1673897984,94118334103159,94118710633777)]
theorem point_links_checked12740 : (cuts12740.take 3).map (fun c => (1673789441-1+2*2^9*c.k,94117479678264+c.lower,94117856208256+c.upper)) = pointBounds12740 := by
 decide +kernel
def cuts12741 : List PrefixCut := [⟨30,243147118,243147295⟩,
⟨82,658302860,658303344⟩,
⟨128,1039481425,1039482188⟩]
theorem checked12741 : checkPrefixCuts (2^48) 1673920513 9 Manual.Count131072.C012741.packed 128 cuts12741 = true := by
 decide +kernel
def pointBounds12741 : List (Nat × Nat × Nat) := [(1673951232,94118758856813,94119135387738),(1674004480,94119174012555,94119550543787)]
theorem point_links_checked12741 : (cuts12741.take 2).map (fun c => (1673920513-1+2*2^9*c.k,94118515709695+c.lower,94118892240443+c.upper)) = pointBounds12741 := by
 decide +kernel
def cuts12742 : List PrefixCut := [⟨6,48760478,48760513⟩,
⟨58,468597566,468597912⟩,
⟨110,890775147,890775804⟩,
⟨128,1033011155,1033011918⟩]
theorem checked12742 : checkPrefixCuts (2^48) 1674051585 9 Manual.Count131072.C012742.packed 128 cuts12742 = true := by
 decide +kernel
def pointBounds12742 : List (Nat × Nat × Nat) := [(1674057728,94119603951598,94119980483144),(1674110976,94120023788686,94120400320543),(1674164224,94120445966267,94120822498435)]
theorem point_links_checked12742 : (cuts12742.take 3).map (fun c => (1674051585-1+2*2^9*c.k,94119555191120+c.lower,94119931722631+c.upper)) = pointBounds12742 := by
 decide +kernel
def cuts12743 : List PrefixCut := [⟨34,276733751,276733953⟩,
⟨86,700061453,700061972⟩,
⟨128,1047388647,1047389418⟩]
theorem checked12743 : checkPrefixCuts (2^48) 1674182657 9 Manual.Count131072.C012743.packed 128 cuts12743 = true := by
 decide +kernel
def pointBounds12743 : List (Nat × Nat × Nat) := [(1674217472,94120864936026,94121241468502),(1674270720,94121288263728,94121664796521)]
theorem point_links_checked12743 : (cuts12743.take 2).map (fun c => (1674182657-1+2*2^9*c.k,94120588202275+c.lower,94120964734549+c.upper)) = pointBounds12743 := by
 decide +kernel
def cuts12744 : List PrefixCut := [⟨10,80526155,80526217⟩,
⟨62,503994988,503995359⟩,
⟨114,929971798,929972478⟩,
⟨128,1030328180,1030328935⟩]
theorem checked12744 : checkPrefixCuts (2^48) 1674313729 9 Manual.Count131072.C012744.packed 128 cuts12744 = true := by
 decide +kernel
def pointBounds12744 : List (Nat × Nat × Nat) := [(1674323968,94121716117077,94122092650184),(1674377216,94122139585910,94122516119326),(1674430464,94122565562720,94122942096445)]
theorem point_links_checked12744 : (cuts12744.take 3).map (fun c => (1674313729-1+2*2^9*c.k,94121635590922+c.lower,94122012123967+c.upper)) = pointBounds12744 := by
 decide +kernel
def cuts12745 : List PrefixCut := [⟨38,308965056,308965285⟩,
⟨90,725165442,725165976⟩,
⟨128,1033441076,1033441837⟩]
theorem checked12745 : checkPrefixCuts (2^48) 1674444801 9 Manual.Count131072.C012745.packed 128 cuts12745 = true := by
 decide +kernel
def pointBounds12745 : List (Nat × Nat × Nat) := [(1674483712,94122974884158,94123351418187),(1674536960,94123391084544,94123767618878)]
theorem point_links_checked12745 : (cuts12745.take 2).map (fun c => (1674444801-1+2*2^9*c.k,94122665919102+c.lower,94123042452902+c.upper)) = pointBounds12745 := by
 decide +kernel
def cuts12746 : List PrefixCut := [⟨14,113962689,113962775⟩,
⟨66,531481139,531481531⟩,
⟨118,947641743,947642440⟩,
⟨128,1027141034,1027141789⟩]
theorem checked12746 : checkPrefixCuts (2^48) 1674575873 9 Manual.Count131072.C012746.packed 128 cuts12746 = true := by
 decide +kernel
def pointBounds12746 : List (Nat × Nat × Nat) := [(1674590208,94123813322867,94124189857514),(1674643456,94124230841317,94124607376270),(1674696704,94124647001921,94125023537179)]
theorem point_links_checked12746 : (cuts12746.take 3).map (fun c => (1674575873-1+2*2^9*c.k,94123699360178+c.lower,94124075894739+c.upper)) = pointBounds12746 := by
 decide +kernel
def cuts12747 : List PrefixCut := [⟨42,338496917,338497168⟩,
⟨94,760681534,760682093⟩,
⟨128,1039833700,1039834465⟩]
theorem checked12747 : checkPrefixCuts (2^48) 1674706945 9 Manual.Count131072.C012747.packed 128 cuts12747 = true := by
 decide +kernel
def pointBounds12747 : List (Nat × Nat × Nat) := [(1674749952,94125064998129,94125441533696),(1674803200,94125487182746,94125863718621)]
theorem point_links_checked12747 : (cuts12747.take 2).map (fun c => (1674706945-1+2*2^9*c.k,94124726501212+c.lower,94125103036528+c.upper)) = pointBounds12747 := by
 decide +kernel
def cuts12748 : List PrefixCut := [⟨18,148733134,148733243⟩,
⟨70,561815819,561816234⟩,
⟨122,987825324,987826050⟩,
⟨128,1036055129,1036055891⟩]
theorem checked12748 : checkPrefixCuts (2^48) 1674838017 9 Manual.Count131072.C012748.packed 128 cuts12748 = true := by
 decide +kernel
def pointBounds12748 : List (Nat × Nat × Nat) := [(1674856448,94125915068046,94126291604236),(1674909696,94126328150731,94126704687227),(1674962944,94126754160236,94127130697043)]
theorem point_links_checked12748 : (cuts12748.take 3).map (fun c => (1674838017-1+2*2^9*c.k,94125766334912+c.lower,94126142870993+c.upper)) = pointBounds12748 := by
 decide +kernel
def cuts12749 : List PrefixCut := [⟨46,386504499,386504782⟩,
⟨98,803916863,803917452⟩,
⟨128,1043872567,1043873333⟩]
theorem checked12749 : checkPrefixCuts (2^48) 1674969089 9 Manual.Count131072.C012749.packed 128 cuts12749 = true := by
 decide +kernel
def pointBounds12749 : List (Nat × Nat × Nat) := [(1675016192,94127188894540,94127565431666),(1675069440,94127606306904,94127982844336)]
theorem point_links_checked12749 : (cuts12749.take 2).map (fun c => (1674969089-1+2*2^9*c.k,94126802390041+c.lower,94127178926884+c.upper)) = pointBounds12749 := by
 decide +kernel
def cuts12750 : List PrefixCut := [⟨22,175426992,175427122⟩,
⟨74,595501228,595501670⟩,
⟨126,1013545864,1013546609⟩,
⟨128,1029843960,1029844717⟩]
theorem checked12750 : checkPrefixCuts (2^48) 1675100161 9 Manual.Count131072.C012750.packed 128 cuts12750 = true := by
 decide +kernel
def pointBounds12750 : List (Nat × Nat × Nat) := [(1675122688,94128021689600,94128398227339),(1675175936,94128441763836,94128818301887),(1675229184,94128859808472,94129236346826)]
theorem point_links_checked12750 : (cuts12750.take 3).map (fun c => (1675100161-1+2*2^9*c.k,94127846262608+c.lower,94128222800217+c.upper)) = pointBounds12750 := by
 decide +kernel
def cuts12751 : List PrefixCut := [⟨50,399549072,399549368⟩,
⟨102,832688482,832689099⟩,
⟨128,1038668357,1038669127⟩]
theorem checked12751 : checkPrefixCuts (2^48) 1675231233 9 Manual.Count131072.C012751.packed 128 cuts12751 = true := by
 decide +kernel
def pointBounds12751 : List (Nat × Nat × Nat) := [(1675282432,94129275655640,94129652194302),(1675335680,94129708795050,94130085334033)]
theorem point_links_checked12751 : (cuts12751.take 2).map (fun c => (1675231233-1+2*2^9*c.k,94128876106568+c.lower,94129252644934+c.upper)) = pointBounds12751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000085
