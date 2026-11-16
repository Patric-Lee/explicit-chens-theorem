import PlattAssemblyKernel
import PlattCertificates.Count131072.C041920
import PlattCertificates.Count131072.C041921
import PlattCertificates.Count131072.C041922
import PlattCertificates.Count131072.C041923
import PlattCertificates.Count131072.C041924
import PlattCertificates.Count131072.C041925
import PlattCertificates.Count131072.C041926
import PlattCertificates.Count131072.C041927
import PlattCertificates.Count131072.C041928
import PlattCertificates.Count131072.C041929
import PlattCertificates.Count131072.C041930
import PlattCertificates.Count131072.C041931
import PlattCertificates.Count131072.C041932
import PlattCertificates.Count131072.C041933
import PlattCertificates.Count131072.C041934
import PlattCertificates.Count131072.C041935
import PlattCertificates.Count131072.C041936
import PlattCertificates.Count131072.C041937
import PlattCertificates.Count131072.C041938
import PlattCertificates.Count131072.C041939
import PlattCertificates.Count131072.C041940
import PlattCertificates.Count131072.C041941
import PlattCertificates.Count131072.C041942
import PlattCertificates.Count131072.C041943
import PlattCertificates.Count131072.C041944
import PlattCertificates.Count131072.C041945
import PlattCertificates.Count131072.C041946
import PlattCertificates.Count131072.C041947
import PlattCertificates.Count131072.C041948
import PlattCertificates.Count131072.C041949
import PlattCertificates.Count131072.C041950
import PlattCertificates.Count131072.C041951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41920 : List PrefixCut := [⟨25,116101763,116101829⟩,
⟨64,298289255,298289425⟩]
theorem checked41920 : checkPrefixCuts (2^48) 5498470401 10 Manual.Count131072.C041920.packed 64 cuts41920 = true := by
 decide +kernel
def pointBounds41920 : List (Nat × Nat × Nat) := [(5498521600,109454903140346,109455288993493)]
theorem point_links_checked41920 : (cuts41920.take 1).map (fun c => (5498470401-1+2*2^10*c.k,109454787038583+c.lower,109455172891664+c.upper)) = pointBounds41920 := by
 decide +kernel
def cuts41921 : List PrefixCut := [⟨45,209468818,209468944⟩,
⟨64,298794022,298794203⟩]
theorem checked41921 : checkPrefixCuts (2^48) 5498601473 10 Manual.Count131072.C041921.packed 64 cuts41921 = true := by
 decide +kernel
def pointBounds41921 : List (Nat × Nat × Nat) := [(5498693632,109455294796656,109455680650033)]
theorem point_links_checked41921 : (cuts41921.take 1).map (fun c => (5498601473-1+2*2^10*c.k,109455085327838+c.lower,109455471181089+c.upper)) = pointBounds41921 := by
 decide +kernel
def cuts41922 : List PrefixCut := [⟨64,300988044,300988211⟩]
theorem checked41922 : checkPrefixCuts (2^48) 5498732545 10 Manual.Count131072.C041922.packed 64 cuts41922 = true := by
 decide +kernel
def cuts41923 : List PrefixCut := [⟨1,4299777,4299779⟩,
⟨64,295913320,295913496⟩]
theorem checked41923 : checkPrefixCuts (2^48) 5498863617 10 Manual.Count131072.C041923.packed 64 cuts41923 = true := by
 decide +kernel
def pointBounds41923 : List (Nat × Nat × Nat) := [(5498865664,109455689409681,109456075263282)]
theorem point_links_checked41923 : (cuts41923.take 1).map (fun c => (5498863617-1+2*2^10*c.k,109455685109904+c.lower,109456070963503+c.upper)) = pointBounds41923 := by
 decide +kernel
def cuts41924 : List PrefixCut := [⟨21,96998249,96998305⟩,
⟨64,301690273,301690448⟩]
theorem checked41924 : checkPrefixCuts (2^48) 5498994689 10 Manual.Count131072.C041924.packed 64 cuts41924 = true := by
 decide +kernel
def pointBounds41924 : List (Nat × Nat × Nat) := [(5499037696,109456078021473,109456463875304)]
theorem point_links_checked41924 : (cuts41924.take 1).map (fun c => (5498994689-1+2*2^10*c.k,109455981023224+c.lower,109456366876999+c.upper)) = pointBounds41924 := by
 decide +kernel
def cuts41925 : List PrefixCut := [⟨41,189742795,189742908⟩,
⟨64,294670788,294670961⟩]
theorem checked41925 : checkPrefixCuts (2^48) 5499125761 10 Manual.Count131072.C041925.packed 64 cuts41925 = true := by
 decide +kernel
def pointBounds41925 : List (Nat × Nat × Nat) := [(5499209728,109456472456292,109456858310355)]
theorem point_links_checked41925 : (cuts41925.take 1).map (fun c => (5499125761-1+2*2^10*c.k,109456282713497+c.lower,109456668567447+c.upper)) = pointBounds41925 := by
 decide +kernel
def cuts41926 : List PrefixCut := [⟨61,286423377,286423544⟩,
⟨64,299986866,299987041⟩]
theorem checked41926 : checkPrefixCuts (2^48) 5499256833 10 Manual.Count131072.C041926.packed 64 cuts41926 = true := by
 decide +kernel
def pointBounds41926 : List (Nat × Nat × Nat) := [(5499381760,109456863807662,109457249661952)]
theorem point_links_checked41926 : (cuts41926.take 1).map (fun c => (5499256833-1+2*2^10*c.k,109456577384285+c.lower,109456963238408+c.upper)) = pointBounds41926 := by
 decide +kernel
def cuts41927 : List PrefixCut := [⟨64,299416688,299416865⟩]
theorem checked41927 : checkPrefixCuts (2^48) 5499387905 10 Manual.Count131072.C041927.packed 64 cuts41927 = true := by
 decide +kernel
def cuts41928 : List PrefixCut := [⟨17,79126702,79126751⟩,
⟨64,299563101,299563278⟩]
theorem checked41928 : checkPrefixCuts (2^48) 5499518977 10 Manual.Count131072.C041928.packed 64 cuts41928 = true := by
 decide +kernel
def pointBounds41928 : List (Nat × Nat × Nat) := [(5499553792,109457255914541,109457641769065)]
theorem point_links_checked41928 : (cuts41928.take 1).map (fun c => (5499518977-1+2*2^10*c.k,109457176787839+c.lower,109457562642314+c.upper)) = pointBounds41928 := by
 decide +kernel
def cuts41929 : List PrefixCut := [⟨37,173705448,173705551⟩,
⟨64,301961393,301961572⟩]
theorem checked41929 : checkPrefixCuts (2^48) 5499650049 10 Manual.Count131072.C041929.packed 64 cuts41929 = true := by
 decide +kernel
def pointBounds41929 : List (Nat × Nat × Nat) := [(5499725824,109457650056388,109458035911143)]
theorem point_links_checked41929 : (cuts41929.take 1).map (fun c => (5499650049-1+2*2^10*c.k,109457476350940+c.lower,109457862205592+c.upper)) = pointBounds41929 := by
 decide +kernel
def cuts41930 : List PrefixCut := [⟨57,265157088,265157242⟩,
⟨64,297859916,297860090⟩]
theorem checked41930 : checkPrefixCuts (2^48) 5499781121 10 Manual.Count131072.C041930.packed 64 cuts41930 = true := by
 decide +kernel
def pointBounds41930 : List (Nat × Nat × Nat) := [(5499897856,109458043469421,109458429324406)]
theorem point_links_checked41930 : (cuts41930.take 1).map (fun c => (5499781121-1+2*2^10*c.k,109457778312333+c.lower,109458164167164+c.upper)) = pointBounds41930 := by
 decide +kernel
def cuts41931 : List PrefixCut := [⟨64,296880474,296880644⟩]
theorem checked41931 : checkPrefixCuts (2^48) 5499912193 10 Manual.Count131072.C041931.packed 64 cuts41931 = true := by
 decide +kernel
def cuts41932 : List PrefixCut := [⟨13,61463249,61463286⟩,
⟨64,300250997,300251173⟩]
theorem checked41932 : checkPrefixCuts (2^48) 5500043265 10 Manual.Count131072.C041932.packed 64 cuts41932 = true := by
 decide +kernel
def pointBounds41932 : List (Nat × Nat × Nat) := [(5500069888,109458434515972,109458820371184)]
theorem point_links_checked41932 : (cuts41932.take 1).map (fun c => (5500043265-1+2*2^10*c.k,109458373052723+c.lower,109458758907898+c.upper)) = pointBounds41932 := by
 decide +kernel
def cuts41933 : List PrefixCut := [⟨33,153730657,153730747⟩,
⟨64,297122194,297122367⟩]
theorem checked41933 : checkPrefixCuts (2^48) 5500174337 10 Manual.Count131072.C041933.packed 64 cuts41933 = true := by
 decide +kernel
def pointBounds41933 : List (Nat × Nat × Nat) := [(5500241920,109458827034377,109459212889818)]
theorem point_links_checked41933 : (cuts41933.take 1).map (fun c => (5500174337-1+2*2^10*c.k,109458673303720+c.lower,109459059159071+c.upper)) = pointBounds41933 := by
 decide +kernel
def cuts41934 : List PrefixCut := [⟨53,248909870,248910015⟩,
⟨64,300646073,300646248⟩]
theorem checked41934 : checkPrefixCuts (2^48) 5500305409 10 Manual.Count131072.C041934.packed 64 cuts41934 = true := by
 decide +kernel
def pointBounds41934 : List (Nat × Nat × Nat) := [(5500413952,109459219335784,109459605191453)]
theorem point_links_checked41934 : (cuts41934.take 1).map (fun c => (5500305409-1+2*2^10*c.k,109458970425914+c.lower,109459356281438+c.upper)) = pointBounds41934 := by
 decide +kernel
def cuts41935 : List PrefixCut := [⟨64,301048323,301048494⟩]
theorem checked41935 : checkPrefixCuts (2^48) 5500436481 10 Manual.Count131072.C041935.packed 64 cuts41935 = true := by
 decide +kernel
def cuts41936 : List PrefixCut := [⟨9,42165635,42165660⟩,
⟨64,299403646,299403826⟩]
theorem checked41936 : checkPrefixCuts (2^48) 5500567553 10 Manual.Count131072.C041936.packed 64 cuts41936 = true := by
 decide +kernel
def pointBounds41936 : List (Nat × Nat × Nat) := [(5500585984,109459614285945,109460000141840)]
theorem point_links_checked41936 : (cuts41936.take 1).map (fun c => (5500567553-1+2*2^10*c.k,109459572120310+c.lower,109459957976180+c.upper)) = pointBounds41936 := by
 decide +kernel
def cuts41937 : List PrefixCut := [⟨29,137085713,137085797⟩,
⟨64,296786874,296787056⟩]
theorem checked41937 : checkPrefixCuts (2^48) 5500698625 10 Manual.Count131072.C041937.packed 64 cuts41937 = true := by
 decide +kernel
def pointBounds41937 : List (Nat × Nat × Nat) := [(5500758016,109460008609669,109460394465803)]
theorem point_links_checked41937 : (cuts41937.take 1).map (fun c => (5500698625-1+2*2^10*c.k,109459871523956+c.lower,109460257380006+c.upper)) = pointBounds41937 := by
 decide +kernel
def cuts41938 : List PrefixCut := [⟨49,229032728,229032868⟩,
⟨64,299798704,299798883⟩]
theorem checked41938 : checkPrefixCuts (2^48) 5500829697 10 Manual.Count131072.C041938.packed 64 cuts41938 = true := by
 decide +kernel
def pointBounds41938 : List (Nat × Nat × Nat) := [(5500930048,109460397343558,109460783199930)]
theorem point_links_checked41938 : (cuts41938.take 1).map (fun c => (5500829697-1+2*2^10*c.k,109460168310830+c.lower,109460554167062+c.upper)) = pointBounds41938 := by
 decide +kernel
def cuts41939 : List PrefixCut := [⟨64,295698188,295698356⟩]
theorem checked41939 : checkPrefixCuts (2^48) 5500960769 10 Manual.Count131072.C041939.packed 64 cuts41939 = true := by
 decide +kernel
def cuts41940 : List PrefixCut := [⟨5,22974004,22974018⟩,
⟨64,300705434,300705611⟩]
theorem checked41940 : checkPrefixCuts (2^48) 5501091841 10 Manual.Count131072.C041940.packed 64 cuts41940 = true := by
 decide +kernel
def pointBounds41940 : List (Nat × Nat × Nat) := [(5501102080,109460786781726,109461172638319)]
theorem point_links_checked41940 : (cuts41940.take 1).map (fun c => (5501091841-1+2*2^10*c.k,109460763807722+c.lower,109461149664301+c.upper)) = pointBounds41940 := by
 decide +kernel
def cuts41941 : List PrefixCut := [⟨25,116094837,116094904⟩,
⟨64,298702823,298702998⟩]
theorem checked41941 : checkPrefixCuts (2^48) 5501222913 10 Manual.Count131072.C041941.packed 64 cuts41941 = true := by
 decide +kernel
def pointBounds41941 : List (Nat × Nat × Nat) := [(5501274112,109461180607993,109461566464816)]
theorem point_links_checked41941 : (cuts41941.take 1).map (fun c => (5501222913-1+2*2^10*c.k,109461064513156+c.lower,109461450369912+c.upper)) = pointBounds41941 := by
 decide +kernel
def cuts41942 : List PrefixCut := [⟨45,208750051,208750177⟩,
⟨64,296597983,296598163⟩]
theorem checked41942 : checkPrefixCuts (2^48) 5501353985 10 Manual.Count131072.C041942.packed 64 cuts41942 = true := by
 decide +kernel
def pointBounds41942 : List (Nat × Nat × Nat) := [(5501446144,109461571966030,109461957823087)]
theorem point_links_checked41942 : (cuts41942.take 1).map (fun c => (5501353985-1+2*2^10*c.k,109461363215979+c.lower,109461749072910+c.upper)) = pointBounds41942 := by
 decide +kernel
def cuts41943 : List PrefixCut := [⟨64,302116548,302116722⟩]
theorem checked41943 : checkPrefixCuts (2^48) 5501485057 10 Manual.Count131072.C041943.packed 64 cuts41943 = true := by
 decide +kernel
def cuts41944 : List PrefixCut := [⟨1,4604599,4604602⟩,
⟨64,300523306,300523475⟩]
theorem checked41944 : checkPrefixCuts (2^48) 5501616129 10 Manual.Count131072.C041944.packed 64 cuts41944 = true := by
 decide +kernel
def pointBounds41944 : List (Nat × Nat × Nat) := [(5501618176,109461966535109,109462352392397)]
theorem point_links_checked41944 : (cuts41944.take 1).map (fun c => (5501616129-1+2*2^10*c.k,109461961930510+c.lower,109462347787795+c.upper)) = pointBounds41944 := by
 decide +kernel
def cuts41945 : List PrefixCut := [⟨21,94698643,94698703⟩,
⟨64,296934888,296935066⟩]
theorem checked41945 : checkPrefixCuts (2^48) 5501747201 10 Manual.Count131072.C041945.packed 64 cuts41945 = true := by
 decide +kernel
def pointBounds41945 : List (Nat × Nat × Nat) := [(5501790208,109462357152459,109462743009973)]
theorem point_links_checked41945 : (cuts41945.take 1).map (fun c => (5501747201-1+2*2^10*c.k,109462262453816+c.lower,109462648311270+c.upper)) = pointBounds41945 := by
 decide +kernel
def cuts41946 : List PrefixCut := [⟨41,190364106,190364220⟩,
⟨64,299281153,299281331⟩]
theorem checked41946 : checkPrefixCuts (2^48) 5501878273 10 Manual.Count131072.C041946.packed 64 cuts41946 = true := by
 decide +kernel
def pointBounds41946 : List (Nat × Nat × Nat) := [(5501962240,109462749752810,109463135610556)]
theorem point_links_checked41946 : (cuts41946.take 1).map (fun c => (5501878273-1+2*2^10*c.k,109462559388704+c.lower,109462945246336+c.upper)) = pointBounds41946 := by
 decide +kernel
def cuts41947 : List PrefixCut := [⟨61,285973105,285973279⟩,
⟨64,299683281,299683464⟩]
theorem checked41947 : checkPrefixCuts (2^48) 5502009345 10 Manual.Count131072.C041947.packed 64 cuts41947 = true := by
 decide +kernel
def pointBounds41947 : List (Nat × Nat × Nat) := [(5502134272,109463144642962,109463530500946)]
theorem point_links_checked41947 : (cuts41947.take 1).map (fun c => (5502009345-1+2*2^10*c.k,109462858669857+c.lower,109463244527667+c.upper)) = pointBounds41947 := by
 decide +kernel
def cuts41948 : List PrefixCut := [⟨64,298550729,298550907⟩]
theorem checked41948 : checkPrefixCuts (2^48) 5502140417 10 Manual.Count131072.C041948.packed 64 cuts41948 = true := by
 decide +kernel
def cuts41949 : List PrefixCut := [⟨17,79445214,79445263⟩,
⟨64,299259773,299259949⟩]
theorem checked41949 : checkPrefixCuts (2^48) 5502271489 10 Manual.Count131072.C041949.packed 64 cuts41949 = true := by
 decide +kernel
def pointBounds41949 : List (Nat × Nat × Nat) := [(5502306304,109463536349081,109463922207301)]
theorem point_links_checked41949 : (cuts41949.take 1).map (fun c => (5502271489-1+2*2^10*c.k,109463456903867+c.lower,109463842762038+c.upper)) = pointBounds41949 := by
 decide +kernel
def cuts41950 : List PrefixCut := [⟨37,172800088,172800191⟩,
⟨64,301349963,301350138⟩]
theorem checked41950 : checkPrefixCuts (2^48) 5502402561 10 Manual.Count131072.C041950.packed 64 cuts41950 = true := by
 decide +kernel
def pointBounds41950 : List (Nat × Nat × Nat) := [(5502478336,109463928963728,109464314822178)]
theorem point_links_checked41950 : (cuts41950.take 1).map (fun c => (5502402561-1+2*2^10*c.k,109463756163640+c.lower,109464142021987+c.upper)) = pointBounds41950 := by
 decide +kernel
def cuts41951 : List PrefixCut := [⟨57,266252107,266252261⟩,
⟨64,300012782,300012955⟩]
theorem checked41951 : checkPrefixCuts (2^48) 5502533633 10 Manual.Count131072.C041951.packed 64 cuts41951 = true := by
 decide +kernel
def pointBounds41951 : List (Nat × Nat × Nat) := [(5502650368,109464323765710,109464709624386)]
theorem point_links_checked41951 : (cuts41951.take 1).map (fun c => (5502533633-1+2*2^10*c.k,109464057513603+c.lower,109464443372125+c.upper)) = pointBounds41951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000060
