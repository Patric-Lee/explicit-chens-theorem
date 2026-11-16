import PlattAssemblyKernel
import PlattCertificates.Count131072.C014896
import PlattCertificates.Count131072.C014897
import PlattCertificates.Count131072.C014898
import PlattCertificates.Count131072.C014899
import PlattCertificates.Count131072.C014900
import PlattCertificates.Count131072.C014901
import PlattCertificates.Count131072.C014902
import PlattCertificates.Count131072.C014903
import PlattCertificates.Count131072.C014904
import PlattCertificates.Count131072.C014905
import PlattCertificates.Count131072.C014906
import PlattCertificates.Count131072.C014907
import PlattCertificates.Count131072.C014908
import PlattCertificates.Count131072.C014909
import PlattCertificates.Count131072.C014910
import PlattCertificates.Count131072.C014911
import PlattCertificates.Count131072.C014912
import PlattCertificates.Count131072.C014913
import PlattCertificates.Count131072.C014914
import PlattCertificates.Count131072.C014915
import PlattCertificates.Count131072.C014916
import PlattCertificates.Count131072.C014917
import PlattCertificates.Count131072.C014918
import PlattCertificates.Count131072.C014919
import PlattCertificates.Count131072.C014920
import PlattCertificates.Count131072.C014921
import PlattCertificates.Count131072.C014922
import PlattCertificates.Count131072.C014923
import PlattCertificates.Count131072.C014924
import PlattCertificates.Count131072.C014925
import PlattCertificates.Count131072.C014926
import PlattCertificates.Count131072.C014927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14896 : List PrefixCut := [⟨10,68916092,68916138⟩,
⟨70,478664392,478664710⟩,
⟨128,883796245,883796828⟩]
theorem checked14896 : checkPrefixCuts (2^48) 1956380673 9 Manual.Count131072.C014896.packed 128 cuts14896 = true := by
 decide +kernel
def pointBounds14896 : List (Nat × Nat × Nat) := [(1956390912,96177520239710,96177898212776),(1956452352,96177929988010,96178307961348)]
theorem point_links_checked14896 : (cuts14896.take 2).map (fun c => (1956380673-1+2*2^9*c.k,96177451323618+c.lower,96177829296638+c.upper)) = pointBounds14896 := by
 decide +kernel
def cuts14897 : List PrefixCut := [⟨2,14530426,14530436⟩,
⟨62,423965278,423965565⟩,
⟨122,832092531,832093094⟩,
⟨128,874961695,874962285⟩]
theorem checked14897 : checkPrefixCuts (2^48) 1956511745 9 Manual.Count131072.C014897.packed 128 cuts14897 = true := by
 decide +kernel
def pointBounds14897 : List (Nat × Nat × Nat) := [(1956513792,96178349650289,96178727623902),(1956575232,96178759085141,96179137059031),(1956636672,96179167212394,96179545186560)]
theorem point_links_checked14897 : (cuts14897.take 3).map (fun c => (1956511745-1+2*2^9*c.k,96178335119863+c.lower,96178713093466+c.upper)) = pointBounds14897 := by
 decide +kernel
def cuts14898 : List PrefixCut := [⟨54,374451903,374452158⟩,
⟨114,791759987,791760521⟩,
⟨128,885260494,885261093⟩]
theorem checked14898 : checkPrefixCuts (2^48) 1956642817 9 Manual.Count131072.C014898.packed 128 cuts14898 = true := by
 decide +kernel
def pointBounds14898 : List (Nat × Nat × Nat) := [(1956698112,96179584533461,96179962507909),(1956759552,96180001841545,96180379816272)]
theorem point_links_checked14898 : (cuts14898.take 2).map (fun c => (1956642817-1+2*2^9*c.k,96179210081558+c.lower,96179588055751+c.upper)) = pointBounds14898 := by
 decide +kernel
def cuts14899 : List PrefixCut := [⟨46,310416829,310417035⟩,
⟨106,728130124,728130607⟩,
⟨128,879878789,879879374⟩]
theorem checked14899 : checkPrefixCuts (2^48) 1956773889 9 Manual.Count131072.C014899.packed 128 cuts14899 = true := by
 decide +kernel
def pointBounds14899 : List (Nat × Nat × Nat) := [(1956820992,96180405758881,96180783733879),(1956882432,96180823472176,96181201447451)]
theorem point_links_checked14899 : (cuts14899.take 2).map (fun c => (1956773889-1+2*2^9*c.k,96180095342052+c.lower,96180473316844+c.upper)) = pointBounds14899 := by
 decide +kernel
def cuts14900 : List PrefixCut := [⟨38,258472133,258472302⟩,
⟨98,668104672,668105113⟩,
⟨128,879100745,879101327⟩]
theorem checked14900 : checkPrefixCuts (2^48) 1956904961 9 Manual.Count131072.C014900.packed 128 cuts14900 = true := by
 decide +kernel
def pointBounds14900 : List (Nat × Nat × Nat) := [(1956943872,96181233692974,96181611668520),(1957005312,96181643325513,96182021301331)]
theorem point_links_checked14900 : (cuts14900.take 2).map (fun c => (1956904961-1+2*2^9*c.k,96180975220841+c.lower,96181353196218+c.upper)) = pointBounds14900 := by
 decide +kernel
def cuts14901 : List PrefixCut := [⟨30,208547666,208547805⟩,
⟨90,623763573,623763983⟩,
⟨128,875015213,875015791⟩]
theorem checked14901 : checkPrefixCuts (2^48) 1957036033 9 Manual.Count131072.C014901.packed 128 cuts14901 = true := by
 decide +kernel
def pointBounds14901 : List (Nat × Nat × Nat) := [(1957066752,96182062869252,96182440845350),(1957128192,96182478085159,96182856061528)]
theorem point_links_checked14901 : (cuts14901.take 2).map (fun c => (1957036033-1+2*2^9*c.k,96181854321586+c.lower,96182232297545+c.upper)) = pointBounds14901 := by
 decide +kernel
def cuts14902 : List PrefixCut := [⟨22,154459093,154459196⟩,
⟨82,562602027,562602402⟩,
⟨128,874237371,874237953⟩]
theorem checked14902 : checkPrefixCuts (2^48) 1957167105 9 Manual.Count131072.C014902.packed 128 cuts14902 = true := by
 decide +kernel
def pointBounds14902 : List (Nat × Nat × Nat) := [(1957189632,96182883795892,96183261772532),(1957251072,96183291938826,96183669915738)]
theorem point_links_checked14902 : (cuts14902.take 2).map (fun c => (1957167105-1+2*2^9*c.k,96182729336799+c.lower,96183107313336+c.upper)) = pointBounds14902 := by
 decide +kernel
def cuts14903 : List PrefixCut := [⟨14,95200467,95200532⟩,
⟨74,502886388,502886726⟩,
⟨128,874753972,874754561⟩]
theorem checked14903 : checkPrefixCuts (2^48) 1957298177 9 Manual.Count131072.C014903.packed 128 cuts14903 = true := by
 decide +kernel
def pointBounds14903 : List (Nat × Nat × Nat) := [(1957312512,96183698774637,96184076751821),(1957373952,96184106460558,96184484438015)]
theorem point_links_checked14903 : (cuts14903.take 2).map (fun c => (1957298177-1+2*2^9*c.k,96183603574170+c.lower,96183981551289+c.upper)) = pointBounds14903 := by
 decide +kernel
def cuts14904 : List PrefixCut := [⟨6,41126234,41126261⟩,
⟨66,460290292,460290594⟩,
⟨126,879441141,879441718⟩,
⟨128,892525911,892526497⟩]
theorem checked14904 : checkPrefixCuts (2^48) 1957429249 9 Manual.Count131072.C014904.packed 128 cuts14904 = true := by
 decide +kernel
def pointBounds14904 : List (Nat × Nat × Nat) := [(1957435392,96184519454376,96184897432111),(1957496832,96184938618434,96185316596444),(1957558272,96185357769283,96185735747568)]
theorem point_links_checked14904 : (cuts14904.take 3).map (fun c => (1957429249-1+2*2^9*c.k,96184478328142+c.lower,96184856305850+c.upper)) = pointBounds14904 := by
 decide +kernel
def cuts14905 : List PrefixCut := [⟨58,403320887,403321155⟩,
⟨118,809648804,809649343⟩,
⟨128,880963366,880963952⟩]
theorem checked14905 : checkPrefixCuts (2^48) 1957560321 9 Manual.Count131072.C014905.packed 128 cuts14905 = true := by
 decide +kernel
def pointBounds14905 : List (Nat × Nat × Nat) := [(1957619712,96185774174940,96186152153502),(1957681152,96186180502857,96186558481690)]
theorem point_links_checked14905 : (cuts14905.take 2).map (fun c => (1957560321-1+2*2^9*c.k,96185370854053+c.lower,96185748832347+c.upper)) = pointBounds14905 := by
 decide +kernel
def cuts14906 : List PrefixCut := [⟨50,338595090,338595318⟩,
⟨110,750073397,750073903⟩,
⟨128,877453655,877454245⟩]
theorem checked14906 : checkPrefixCuts (2^48) 1957691393 9 Manual.Count131072.C014906.packed 128 cuts14906 = true := by
 decide +kernel
def pointBounds14906 : List (Nat × Nat × Nat) := [(1957742592,96186590412509,96186968391617),(1957804032,96187001890816,96187379870202)]
theorem point_links_checked14906 : (cuts14906.take 2).map (fun c => (1957691393-1+2*2^9*c.k,96186251817419+c.lower,96186629796299+c.upper)) = pointBounds14906 := by
 decide +kernel
def cuts14907 : List PrefixCut := [⟨42,289979633,289979825⟩,
⟨102,704019846,704020314⟩,
⟨128,882139392,882139978⟩]
theorem checked14907 : checkPrefixCuts (2^48) 1957822465 9 Manual.Count131072.C014907.packed 128 cuts14907 = true := by
 decide +kernel
def pointBounds14907 : List (Nat × Nat × Nat) := [(1957865472,96187419250707,96187797230369),(1957926912,96187833290920,96188211270858)]
theorem point_links_checked14907 : (cuts14907.take 2).map (fun c => (1957822465-1+2*2^9*c.k,96187129271074+c.lower,96187507250544+c.upper)) = pointBounds14907 := by
 decide +kernel
def cuts14908 : List PrefixCut := [⟨34,241945476,241945631⟩,
⟨94,663578690,663579129⟩,
⟨128,893580916,893581507⟩]
theorem checked14908 : checkPrefixCuts (2^48) 1957953537 9 Manual.Count131072.C014908.packed 128 cuts14908 = true := by
 decide +kernel
def pointBounds14908 : List (Nat × Nat × Nat) := [(1957988352,96188253355942,96188631336153),(1958049792,96188674989156,96189052969651)]
theorem point_links_checked14908 : (cuts14908.take 2).map (fun c => (1957953537-1+2*2^9*c.k,96188011410466+c.lower,96188389390522+c.upper)) = pointBounds14908 := by
 decide +kernel
def cuts14909 : List PrefixCut := [⟨26,174367695,174367812⟩,
⟨86,582893511,582893900⟩,
⟨128,869658938,869659520⟩]
theorem checked14909 : checkPrefixCuts (2^48) 1958084609 9 Manual.Count131072.C014909.packed 128 cuts14909 = true := by
 decide +kernel
def pointBounds14909 : List (Nat × Nat × Nat) := [(1958111232,96189079359077,96189457339841),(1958172672,96189487884893,96189865865929)]
theorem point_links_checked14909 : (cuts14909.take 2).map (fun c => (1958084609-1+2*2^9*c.k,96188904991382+c.lower,96189282972029+c.upper)) = pointBounds14909 := by
 decide +kernel
def cuts14910 : List PrefixCut := [⟨18,128215917,128216003⟩,
⟨78,550946004,550946366⟩,
⟨128,888286759,888287349⟩]
theorem checked14910 : checkPrefixCuts (2^48) 1958215681 9 Manual.Count131072.C014910.packed 128 cuts14910 = true := by
 decide +kernel
def pointBounds14910 : List (Nat × Nat × Nat) := [(1958234112,96189902866237,96190280847552),(1958295552,96190325596324,96190703577915)]
theorem point_links_checked14910 : (cuts14910.take 2).map (fun c => (1958215681-1+2*2^9*c.k,96189774650320+c.lower,96190152631549+c.upper)) = pointBounds14910 := by
 decide +kernel
def cuts14911 : List PrefixCut := [⟨10,68703179,68703223⟩,
⟨70,479621149,479621465⟩,
⟨128,872273557,872274138⟩]
theorem checked14911 : checkPrefixCuts (2^48) 1958346753 9 Manual.Count131072.C014911.packed 128 cuts14911 = true := by
 decide +kernel
def pointBounds14911 : List (Nat × Nat × Nat) := [(1958356992,96190731640258,96191109622121),(1958418432,96191142558228,96191520540363)]
theorem point_links_checked14911 : (cuts14911.take 2).map (fun c => (1958346753-1+2*2^9*c.k,96190662937079+c.lower,96191040918898+c.upper)) = pointBounds14911 := by
 decide +kernel
def cuts14912 : List PrefixCut := [⟨2,11928857,11928865⟩,
⟨62,430725579,430725865⟩,
⟨122,836000013,836000568⟩,
⟨128,874945926,874946507⟩]
theorem checked14912 : checkPrefixCuts (2^48) 1958477825 9 Manual.Count131072.C014912.packed 128 cuts14912 = true := by
 decide +kernel
def pointBounds14912 : List (Nat × Nat × Nat) := [(1958479872,96191547139493,96191925121901),(1958541312,96191965936215,96192343918901),(1958602752,96192371210649,96192749193604)]
theorem point_links_checked14912 : (cuts14912.take 3).map (fun c => (1958477825-1+2*2^9*c.k,96191535210636+c.lower,96191913193036+c.upper)) = pointBounds14912 := by
 decide +kernel
def cuts14913 : List PrefixCut := [⟨54,372495347,372495597⟩,
⟨114,792689674,792690202⟩,
⟨128,886383727,886384318⟩]
theorem checked14913 : checkPrefixCuts (2^48) 1958608897 9 Manual.Count131072.C014913.packed 128 cuts14913 = true := by
 decide +kernel
def pointBounds14913 : List (Nat × Nat × Nat) := [(1958664192,96192782651909,96193160635140),(1958725632,96193202846236,96193580829745)]
theorem point_links_checked14913 : (cuts14913.take 2).map (fun c => (1958608897-1+2*2^9*c.k,96192410156562+c.lower,96192788139543+c.upper)) = pointBounds14913 := by
 decide +kernel
def cuts14914 : List PrefixCut := [⟨46,315565842,315566057⟩,
⟨106,726393547,726394041⟩,
⟨128,880145287,880145882⟩]
theorem checked14914 : checkPrefixCuts (2^48) 1958739969 9 Manual.Count131072.C014914.packed 128 cuts14914 = true := by
 decide +kernel
def pointBounds14914 : List (Nat × Nat × Nat) := [(1958787072,96193612106131,96193990089918),(1958848512,96194022933836,96194400917902)]
theorem point_links_checked14914 : (cuts14914.take 2).map (fun c => (1958739969-1+2*2^9*c.k,96193296540289+c.lower,96193674523861+c.upper)) = pointBounds14914 := by
 decide +kernel
def cuts14915 : List PrefixCut := [⟨38,258931138,258931309⟩,
⟨98,666140926,666141371⟩,
⟨128,870890505,870891087⟩]
theorem checked14915 : checkPrefixCuts (2^48) 1958871041 9 Manual.Count131072.C014915.packed 128 cuts14915 = true := by
 decide +kernel
def pointBounds14915 : List (Nat × Nat × Nat) := [(1958909952,96194435616714,96194813601052),(1958971392,96194842826502,96195220811114)]
theorem point_links_checked14915 : (cuts14915.take 2).map (fun c => (1958871041-1+2*2^9*c.k,96194176685576+c.lower,96194554669743+c.upper)) = pointBounds14915 := by
 decide +kernel
def cuts14916 : List PrefixCut := [⟨30,210780982,210781122⟩,
⟨90,633195122,633195537⟩,
⟨128,885200362,885200945⟩]
theorem checked14916 : checkPrefixCuts (2^48) 1959002113 9 Manual.Count131072.C014916.packed 128 cuts14916 = true := by
 decide +kernel
def pointBounds14916 : List (Nat × Nat × Nat) := [(1959032832,96195258357063,96195636341952),(1959094272,96195680771203,96196058756367)]
theorem point_links_checked14916 : (cuts14916.take 2).map (fun c => (1959002113-1+2*2^9*c.k,96195047576081+c.lower,96195425560830+c.upper)) = pointBounds14916 := by
 decide +kernel
def cuts14917 : List PrefixCut := [⟨22,153011048,153011147⟩,
⟨82,571088615,571088993⟩,
⟨128,897496122,897496719⟩]
theorem checked14917 : checkPrefixCuts (2^48) 1959133185 9 Manual.Count131072.C014917.packed 128 cuts14917 = true := by
 decide +kernel
def pointBounds14917 : List (Nat × Nat × Nat) := [(1959155712,96196085787491,96196463772922),(1959217152,96196503865058,96196881850768)]
theorem point_links_checked14917 : (cuts14917.take 2).map (fun c => (1959133185-1+2*2^9*c.k,96195932776443+c.lower,96196310761775+c.upper)) = pointBounds14917 := by
 decide +kernel
def cuts14918 : List PrefixCut := [⟨14,93955618,93955685⟩,
⟨74,507840806,507841146⟩,
⟨128,882495538,882496127⟩]
theorem checked14918 : checkPrefixCuts (2^48) 1959264257 9 Manual.Count131072.C014918.packed 128 cuts14918 = true := by
 decide +kernel
def pointBounds14918 : List (Nat × Nat × Nat) := [(1959278592,96196924228183,96197302214179),(1959340032,96197338113371,96197716099640)]
theorem point_links_checked14918 : (cuts14918.take 2).map (fun c => (1959264257-1+2*2^9*c.k,96196830272565+c.lower,96197208258494+c.upper)) = pointBounds14918 := by
 decide +kernel
def cuts14919 : List PrefixCut := [⟨6,42521501,42521530⟩,
⟨66,465574493,465574805⟩,
⟨126,891774368,891774963⟩,
⟨128,907000677,907001282⟩]
theorem checked14919 : checkPrefixCuts (2^48) 1959395329 9 Manual.Count131072.C014919.packed 128 cuts14919 = true := by
 decide +kernel
def pointBounds14919 : List (Nat × Nat × Nat) := [(1959401472,96197755289604,96198133276151),(1959462912,96198178342596,96198556329426),(1959524352,96198604542471,96198982529584)]
theorem point_links_checked14919 : (cuts14919.take 3).map (fun c => (1959395329-1+2*2^9*c.k,96197712768103+c.lower,96198090754621+c.upper)) = pointBounds14919 := by
 decide +kernel
def cuts14920 : List PrefixCut := [⟨58,387546566,387546828⟩,
⟨118,795621400,795621939⟩,
⟨128,863273541,863274125⟩]
theorem checked14920 : checkPrefixCuts (2^48) 1959526401 9 Manual.Count131072.C014920.packed 128 cuts14920 = true := by
 decide +kernel
def pointBounds14920 : List (Nat × Nat × Nat) := [(1959585792,96199007315346,96199385302731),(1959647232,96199415390180,96199793377842)]
theorem point_links_checked14920 : (cuts14920.take 2).map (fun c => (1959526401-1+2*2^9*c.k,96198619768780+c.lower,96198997755903+c.upper)) = pointBounds14920 := by
 decide +kernel
def cuts14921 : List PrefixCut := [⟨50,346873301,346873535⟩,
⟨110,755927857,755928362⟩,
⟨128,878153417,878154003⟩]
theorem checked14921 : checkPrefixCuts (2^48) 1959657473 9 Manual.Count131072.C014921.packed 128 cuts14921 = true := by
 decide +kernel
def pointBounds14921 : List (Nat × Nat × Nat) := [(1959708672,96199829915622,96200207903563),(1959770112,96200238970178,96200616958390)]
theorem point_links_checked14921 : (cuts14921.take 2).map (fun c => (1959657473-1+2*2^9*c.k,96199483042321+c.lower,96199861030028+c.upper)) = pointBounds14921 := by
 decide +kernel
def cuts14922 : List PrefixCut := [⟨42,287534359,287534555⟩,
⟨102,698143117,698143588⟩,
⟨128,874647797,874648389⟩]
theorem checked14922 : checkPrefixCuts (2^48) 1959788545 9 Manual.Count131072.C014922.packed 128 cuts14922 = true := by
 decide +kernel
def pointBounds14922 : List (Nat × Nat × Nat) := [(1959831552,96200648730097,96201026718586),(1959892992,96201059338855,96201437327619)]
theorem point_links_checked14922 : (cuts14922.take 2).map (fun c => (1959788545-1+2*2^9*c.k,96200361195738+c.lower,96200739184031+c.upper)) = pointBounds14922 := by
 decide +kernel
def cuts14923 : List PrefixCut := [⟨34,221883986,221884141⟩,
⟨94,624568433,624568863⟩,
⟨128,861663900,861664488⟩]
theorem checked14923 : checkPrefixCuts (2^48) 1959919617 9 Manual.Count131072.C014923.packed 128 cuts14923 = true := by
 decide +kernel
def pointBounds14923 : List (Nat × Nat × Nat) := [(1959954432,96201457727521,96201835716561),(1960015872,96201860411968,96202238401283)]
theorem point_links_checked14923 : (cuts14923.take 2).map (fun c => (1959919617-1+2*2^9*c.k,96201235843535+c.lower,96201613832420+c.upper)) = pointBounds14923 := by
 decide +kernel
def cuts14924 : List PrefixCut := [⟨26,173331155,173331273⟩,
⟨86,583457654,583458048⟩,
⟨128,869217478,869218059⟩]
theorem checked14924 : checkPrefixCuts (2^48) 1960050689 9 Manual.Count131072.C014924.packed 128 cuts14924 = true := by
 decide +kernel
def pointBounds14924 : List (Nat × Nat × Nat) := [(1960077312,96202270838590,96202648828181),(1960138752,96202680965089,96203058954956)]
theorem point_links_checked14924 : (cuts14924.take 2).map (fun c => (1960050689-1+2*2^9*c.k,96202097507435+c.lower,96202475496908+c.upper)) = pointBounds14924 := by
 decide +kernel
def cuts14925 : List PrefixCut := [⟨18,119184386,119184465⟩,
⟨78,539049438,539049794⟩,
⟨128,879641530,879642111⟩]
theorem checked14925 : checkPrefixCuts (2^48) 1960181761 9 Manual.Count131072.C014925.packed 128 cuts14925 = true := by
 decide +kernel
def pointBounds14925 : List (Nat × Nat × Nat) := [(1960200192,96203085909299,96203463899432),(1960261632,96203505774351,96203883764761)]
theorem point_links_checked14925 : (cuts14925.take 2).map (fun c => (1960181761-1+2*2^9*c.k,96202966724913+c.lower,96203344714967+c.upper)) = pointBounds14925 := by
 decide +kernel
def cuts14926 : List PrefixCut := [⟨10,66193308,66193354⟩,
⟨70,483160445,483160772⟩,
⟨128,877859868,877860461⟩]
theorem checked14926 : checkPrefixCuts (2^48) 1960312833 9 Manual.Count131072.C014926.packed 128 cuts14926 = true := by
 decide +kernel
def pointBounds14926 : List (Nat × Nat × Nat) := [(1960323072,96203912559751,96204290550432),(1960384512,96204329526888,96204707517850)]
theorem point_links_checked14926 : (cuts14926.take 2).map (fun c => (1960312833-1+2*2^9*c.k,96203846366443+c.lower,96204224357078+c.upper)) = pointBounds14926 := by
 decide +kernel
def cuts14927 : List PrefixCut := [⟨2,13783396,13783406⟩,
⟨62,421104874,421105154⟩,
⟨122,826834297,826834846⟩,
⟨128,873924516,873925096⟩]
theorem checked14927 : checkPrefixCuts (2^48) 1960443905 9 Manual.Count131072.C014927.packed 128 cuts14927 = true := by
 decide +kernel
def pointBounds14927 : List (Nat × Nat × Nat) := [(1960445952,96204738009707,96205116000945),(1960507392,96205145331185,96205523322693),(1960568832,96205551060608,96205929052385)]
theorem point_links_checked14927 : (cuts14927.take 3).map (fun c => (1960443905-1+2*2^9*c.k,96204724226311+c.lower,96205102217539+c.upper)) = pointBounds14927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000153
