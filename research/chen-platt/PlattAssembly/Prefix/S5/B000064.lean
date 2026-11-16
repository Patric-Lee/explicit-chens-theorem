import PlattAssemblyKernel
import PlattCertificates.Count131072.C042048
import PlattCertificates.Count131072.C042049
import PlattCertificates.Count131072.C042050
import PlattCertificates.Count131072.C042051
import PlattCertificates.Count131072.C042052
import PlattCertificates.Count131072.C042053
import PlattCertificates.Count131072.C042054
import PlattCertificates.Count131072.C042055
import PlattCertificates.Count131072.C042056
import PlattCertificates.Count131072.C042057
import PlattCertificates.Count131072.C042058
import PlattCertificates.Count131072.C042059
import PlattCertificates.Count131072.C042060
import PlattCertificates.Count131072.C042061
import PlattCertificates.Count131072.C042062
import PlattCertificates.Count131072.C042063
import PlattCertificates.Count131072.C042064
import PlattCertificates.Count131072.C042065
import PlattCertificates.Count131072.C042066
import PlattCertificates.Count131072.C042067
import PlattCertificates.Count131072.C042068
import PlattCertificates.Count131072.C042069
import PlattCertificates.Count131072.C042070
import PlattCertificates.Count131072.C042071
import PlattCertificates.Count131072.C042072
import PlattCertificates.Count131072.C042073
import PlattCertificates.Count131072.C042074
import PlattCertificates.Count131072.C042075
import PlattCertificates.Count131072.C042076
import PlattCertificates.Count131072.C042077
import PlattCertificates.Count131072.C042078
import PlattCertificates.Count131072.C042079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42048 : List PrefixCut := [⟨40,189086129,189086240⟩,
⟨64,298402626,298402803⟩]
theorem checked42048 : checkPrefixCuts (2^48) 5515247617 10 Manual.Count131072.C042048.packed 64 cuts42048 = true := by
 decide +kernel
def pointBounds42048 : List (Nat × Nat × Nat) := [(5515329536,109493194190176,109493580065744)]
theorem point_links_checked42048 : (cuts42048.take 1).map (fun c => (5515247617-1+2*2^10*c.k,109493005104047+c.lower,109493390979504+c.upper)) = pointBounds42048 := by
 decide +kernel
def cuts42049 : List PrefixCut := [⟨61,283850990,283851156⟩,
⟨64,298089299,298089474⟩]
theorem checked42049 : checkPrefixCuts (2^48) 5515378689 10 Manual.Count131072.C042049.packed 64 cuts42049 = true := by
 decide +kernel
def pointBounds42049 : List (Nat × Nat × Nat) := [(5515503616,109493587357663,109493973233463)]
theorem point_links_checked42049 : (cuts42049.take 1).map (fun c => (5515378689-1+2*2^10*c.k,109493303506673+c.lower,109493689382307+c.upper)) = pointBounds42049 := by
 decide +kernel
def cuts42050 : List PrefixCut := [⟨64,298694582,298694760⟩]
theorem checked42050 : checkPrefixCuts (2^48) 5515509761 10 Manual.Count131072.C042050.packed 64 cuts42050 = true := by
 decide +kernel
def cuts42051 : List PrefixCut := [⟨18,85784724,85784773⟩,
⟨64,302259716,302259887⟩]
theorem checked42051 : checkPrefixCuts (2^48) 5515640833 10 Manual.Count131072.C042051.packed 64 cuts42051 = true := by
 decide +kernel
def pointBounds42051 : List (Nat × Nat × Nat) := [(5515677696,109493986075278,109494371951314)]
theorem point_links_checked42051 : (cuts42051.take 1).map (fun c => (5515640833-1+2*2^10*c.k,109493900290554+c.lower,109494286166541+c.upper)) = pointBounds42051 := by
 decide +kernel
def cuts42052 : List PrefixCut := [⟨39,187945501,187945606⟩,
⟨64,302813895,302814069⟩]
theorem checked42052 : checkPrefixCuts (2^48) 5515771905 10 Manual.Count131072.C042052.packed 64 cuts42052 = true := by
 decide +kernel
def pointBounds42052 : List (Nat × Nat × Nat) := [(5515851776,109494390495771,109494776372034)]
theorem point_links_checked42052 : (cuts42052.take 1).map (fun c => (5515771905-1+2*2^10*c.k,109494202550270+c.lower,109494588426428+c.upper)) = pointBounds42052 := by
 decide +kernel
def cuts42053 : List PrefixCut := [⟨60,279078324,279078487⟩,
⟨64,297346537,297346712⟩]
theorem checked42053 : checkPrefixCuts (2^48) 5515902977 10 Manual.Count131072.C042053.packed 64 cuts42053 = true := by
 decide +kernel
def pointBounds42053 : List (Nat × Nat × Nat) := [(5516025856,109494784442489,109495170318984)]
theorem point_links_checked42053 : (cuts42053.take 1).map (fun c => (5515902977-1+2*2^10*c.k,109494505364165+c.lower,109494891240497+c.upper)) = pointBounds42053 := by
 decide +kernel
def cuts42054 : List PrefixCut := [⟨64,297543576,297543748⟩]
theorem checked42054 : checkPrefixCuts (2^48) 5516034049 10 Manual.Count131072.C042054.packed 64 cuts42054 = true := by
 decide +kernel
def cuts42055 : List PrefixCut := [⟨17,80316685,80316731⟩,
⟨64,297638595,297638767⟩]
theorem checked42055 : checkPrefixCuts (2^48) 5516165121 10 Manual.Count131072.C042055.packed 64 cuts42055 = true := by
 decide +kernel
def pointBounds42055 : List (Nat × Nat × Nat) := [(5516199936,109495180570963,109495566447688)]
theorem point_links_checked42055 : (cuts42055.take 1).map (fun c => (5516165121-1+2*2^10*c.k,109495100254278+c.lower,109495486130957+c.upper)) = pointBounds42055 := by
 decide +kernel
def cuts42056 : List PrefixCut := [⟨38,177467408,177467509⟩,
⟨64,298141772,298141942⟩]
theorem checked42056 : checkPrefixCuts (2^48) 5516296193 10 Manual.Count131072.C042056.packed 64 cuts42056 = true := by
 decide +kernel
def pointBounds42056 : List (Nat × Nat × Nat) := [(5516374016,109495575360281,109495961237233)]
theorem point_links_checked42056 : (cuts42056.take 1).map (fun c => (5516296193-1+2*2^10*c.k,109495397892873+c.lower,109495783769724+c.upper)) = pointBounds42056 := by
 decide +kernel
def cuts42057 : List PrefixCut := [⟨59,273082051,273082213⟩,
⟨64,296399877,296400053⟩]
theorem checked42057 : checkPrefixCuts (2^48) 5516427265 10 Manual.Count131072.C042057.packed 64 cuts42057 = true := by
 decide +kernel
def pointBounds42057 : List (Nat × Nat × Nat) := [(5516548096,109495969116696,109496354993879)]
theorem point_links_checked42057 : (cuts42057.take 1).map (fun c => (5516427265-1+2*2^10*c.k,109495696034645+c.lower,109496081911666+c.upper)) = pointBounds42057 := by
 decide +kernel
def cuts42058 : List PrefixCut := [⟨64,300576712,300576884⟩]
theorem checked42058 : checkPrefixCuts (2^48) 5516558337 10 Manual.Count131072.C042058.packed 64 cuts42058 = true := by
 decide +kernel
def cuts42059 : List PrefixCut := [⟨16,73880262,73880307⟩,
⟨64,297610287,297610463⟩]
theorem checked42059 : checkPrefixCuts (2^48) 5516689409 10 Manual.Count131072.C042059.packed 64 cuts42059 = true := by
 decide +kernel
def pointBounds42059 : List (Nat × Nat × Nat) := [(5516722176,109496366891496,109496752768910)]
theorem point_links_checked42059 : (cuts42059.take 1).map (fun c => (5516689409-1+2*2^10*c.k,109496293011234+c.lower,109496678888603+c.upper)) = pointBounds42059 := by
 decide +kernel
def cuts42060 : List PrefixCut := [⟨37,173317890,173317991⟩,
⟨64,298062419,298062594⟩]
theorem checked42060 : checkPrefixCuts (2^48) 5516820481 10 Manual.Count131072.C042060.packed 64 cuts42060 = true := by
 decide +kernel
def pointBounds42060 : List (Nat × Nat × Nat) := [(5516896256,109496763939411,109497149817057)]
theorem point_links_checked42060 : (cuts42060.take 1).map (fun c => (5516820481-1+2*2^10*c.k,109496590621521+c.lower,109496976499066+c.upper)) = pointBounds42060 := by
 decide +kernel
def cuts42061 : List PrefixCut := [⟨58,272443889,272444048⟩,
⟨64,302545010,302545187⟩]
theorem checked42061 : checkPrefixCuts (2^48) 5516951553 10 Manual.Count131072.C042061.packed 64 cuts42061 = true := by
 decide +kernel
def pointBounds42061 : List (Nat × Nat × Nat) := [(5517070336,109497161127829,109497547005708)]
theorem point_links_checked42061 : (cuts42061.take 1).map (fun c => (5516951553-1+2*2^10*c.k,109496888683940+c.lower,109497274561660+c.upper)) = pointBounds42061 := by
 decide +kernel
def cuts42062 : List PrefixCut := [⟨64,298456373,298456551⟩]
theorem checked42062 : checkPrefixCuts (2^48) 5517082625 10 Manual.Count131072.C042062.packed 64 cuts42062 = true := by
 decide +kernel
def cuts42063 : List PrefixCut := [⟨15,69434736,69434776⟩,
⟨64,298500310,298500485⟩]
theorem checked42063 : checkPrefixCuts (2^48) 5517213697 10 Manual.Count131072.C042063.packed 64 cuts42063 = true := by
 decide +kernel
def pointBounds42063 : List (Nat × Nat × Nat) := [(5517244416,109497559120059,109497944998174)]
theorem point_links_checked42063 : (cuts42063.take 1).map (fun c => (5517213697-1+2*2^10*c.k,109497489685323+c.lower,109497875563398+c.upper)) = pointBounds42063 := by
 decide +kernel
def cuts42064 : List PrefixCut := [⟨36,166312247,166312345⟩,
⟨64,297115792,297115968⟩]
theorem checked42064 : checkPrefixCuts (2^48) 5517344769 10 Manual.Count131072.C042064.packed 64 cuts42064 = true := by
 decide +kernel
def pointBounds42064 : List (Nat × Nat × Nat) := [(5517418496,109497954497880,109498340376228)]
theorem point_links_checked42064 : (cuts42064.take 1).map (fun c => (5517344769-1+2*2^10*c.k,109497788185633+c.lower,109498174063883+c.upper)) = pointBounds42064 := by
 decide +kernel
def cuts42065 : List PrefixCut := [⟨57,263898588,263898740⟩,
⟨64,297771890,297772062⟩]
theorem checked42065 : checkPrefixCuts (2^48) 5517475841 10 Manual.Count131072.C042065.packed 64 cuts42065 = true := by
 decide +kernel
def pointBounds42065 : List (Nat × Nat × Nat) := [(5517592576,109498349200013,109498735078591)]
theorem point_links_checked42065 : (cuts42065.take 1).map (fun c => (5517475841-1+2*2^10*c.k,109498085301425+c.lower,109498471179851+c.upper)) = pointBounds42065 := by
 decide +kernel
def cuts42066 : List PrefixCut := [⟨64,299703348,299703520⟩]
theorem checked42066 : checkPrefixCuts (2^48) 5517606913 10 Manual.Count131072.C042066.packed 64 cuts42066 = true := by
 decide +kernel
def cuts42067 : List PrefixCut := [⟨14,66469418,66469455⟩,
⟨64,296941603,296941774⟩]
theorem checked42067 : checkPrefixCuts (2^48) 5517737985 10 Manual.Count131072.C042067.packed 64 cuts42067 = true := by
 decide +kernel
def pointBounds42067 : List (Nat × Nat × Nat) := [(5517766656,109498749246081,109499135124888)]
theorem point_links_checked42067 : (cuts42067.take 1).map (fun c => (5517737985-1+2*2^10*c.k,109498682776663+c.lower,109499068655433+c.upper)) = pointBounds42067 := by
 decide +kernel
def cuts42068 : List PrefixCut := [⟨35,162368612,162368708⟩,
⟨64,299740127,299740302⟩]
theorem checked42068 : checkPrefixCuts (2^48) 5517869057 10 Manual.Count131072.C042068.packed 64 cuts42068 = true := by
 decide +kernel
def pointBounds42068 : List (Nat × Nat × Nat) := [(5517940736,109499142086878,109499527965915)]
theorem point_links_checked42068 : (cuts42068.take 1).map (fun c => (5517869057-1+2*2^10*c.k,109498979718266+c.lower,109499365597207+c.upper)) = pointBounds42068 := by
 decide +kernel
def cuts42069 : List PrefixCut := [⟨56,256528183,256528328⟩,
⟨64,294121944,294122110⟩]
theorem checked42069 : checkPrefixCuts (2^48) 5518000129 10 Manual.Count131072.C042069.packed 64 cuts42069 = true := by
 decide +kernel
def pointBounds42069 : List (Nat × Nat × Nat) := [(5518114816,109499535986576,109499921865837)]
theorem point_links_checked42069 : (cuts42069.take 1).map (fun c => (5518000129-1+2*2^10*c.k,109499279458393+c.lower,109499665337509+c.upper)) = pointBounds42069 := by
 decide +kernel
def cuts42070 : List PrefixCut := [⟨64,294625062,294625242⟩]
theorem checked42070 : checkPrefixCuts (2^48) 5518131201 10 Manual.Count131072.C042070.packed 64 cuts42070 = true := by
 decide +kernel
def cuts42071 : List PrefixCut := [⟨13,59628077,59628113⟩,
⟨64,294975099,294975273⟩]
theorem checked42071 : checkPrefixCuts (2^48) 5518262273 10 Manual.Count131072.C042071.packed 64 cuts42071 = true := by
 decide +kernel
def pointBounds42071 : List (Nat × Nat × Nat) := [(5518288896,109499927833476,109500313712974)]
theorem point_links_checked42071 : (cuts42071.take 1).map (fun c => (5518262273-1+2*2^10*c.k,109499868205399+c.lower,109500254084861+c.upper)) = pointBounds42071 := by
 decide +kernel
def cuts42072 : List PrefixCut := [⟨34,160669997,160670091⟩,
⟨64,299405626,299405804⟩]
theorem checked42072 : checkPrefixCuts (2^48) 5518393345 10 Manual.Count131072.C042072.packed 64 cuts42072 = true := by
 decide +kernel
def pointBounds42072 : List (Nat × Nat × Nat) := [(5518462976,109500323850495,109500709730225)]
theorem point_links_checked42072 : (cuts42072.take 1).map (fun c => (5518393345-1+2*2^10*c.k,109500163180498+c.lower,109500549060134+c.upper)) = pointBounds42072 := by
 decide +kernel
def cuts42073 : List PrefixCut := [⟨55,254463673,254463824⟩,
⟨64,297613343,297613520⟩]
theorem checked42073 : checkPrefixCuts (2^48) 5518524417 10 Manual.Count131072.C042073.packed 64 cuts42073 = true := by
 decide +kernel
def pointBounds42073 : List (Nat × Nat × Nat) := [(5518637056,109500717049797,109501102929762)]
theorem point_links_checked42073 : (cuts42073.take 1).map (fun c => (5518524417-1+2*2^10*c.k,109500462586124+c.lower,109500848465938+c.upper)) = pointBounds42073 := by
 decide +kernel
def cuts42074 : List PrefixCut := [⟨64,300054465,300054645⟩]
theorem checked42074 : checkPrefixCuts (2^48) 5518655489 10 Manual.Count131072.C042074.packed 64 cuts42074 = true := by
 decide +kernel
def cuts42075 : List PrefixCut := [⟨12,54369123,54369156⟩,
⟨64,296069143,296069317⟩]
theorem checked42075 : checkPrefixCuts (2^48) 5518786561 10 Manual.Count131072.C042075.packed 64 cuts42075 = true := by
 decide +kernel
def pointBounds42075 : List (Nat × Nat × Nat) := [(5518811136,109501114623055,109501500503259)]
theorem point_links_checked42075 : (cuts42075.take 1).map (fun c => (5518786561-1+2*2^10*c.k,109501060253932+c.lower,109501446134103+c.upper)) = pointBounds42075 := by
 decide +kernel
def cuts42076 : List PrefixCut := [⟨33,153106549,153106642⟩,
⟨64,298714155,298714334⟩]
theorem checked42076 : checkPrefixCuts (2^48) 5518917633 10 Manual.Count131072.C042076.packed 64 cuts42076 = true := by
 decide +kernel
def pointBounds42076 : List (Nat × Nat × Nat) := [(5518985216,109501509429624,109501895310062)]
theorem point_links_checked42076 : (cuts42076.take 1).map (fun c => (5518917633-1+2*2^10*c.k,109501356323075+c.lower,109501742203420+c.upper)) = pointBounds42076 := by
 decide +kernel
def cuts42077 : List PrefixCut := [⟨54,249339532,249339681⟩,
⟨64,296259073,296259251⟩]
theorem checked42077 : checkPrefixCuts (2^48) 5519048705 10 Manual.Count131072.C042077.packed 64 cuts42077 = true := by
 decide +kernel
def pointBounds42077 : List (Nat × Nat × Nat) := [(5519159296,109501904376762,109502290257435)]
theorem point_links_checked42077 : (cuts42077.take 1).map (fun c => (5519048705-1+2*2^10*c.k,109501655037230+c.lower,109502040917754+c.upper)) = pointBounds42077 := by
 decide +kernel
def cuts42078 : List PrefixCut := [⟨64,295793036,295793211⟩]
theorem checked42078 : checkPrefixCuts (2^48) 5519179777 10 Manual.Count131072.C042078.packed 64 cuts42078 = true := by
 decide +kernel
def cuts42079 : List PrefixCut := [⟨11,54108975,54109003⟩,
⟨64,298998907,298999084⟩]
theorem checked42079 : checkPrefixCuts (2^48) 5519310849 10 Manual.Count131072.C042079.packed 64 cuts42079 = true := by
 decide +kernel
def pointBounds42079 : List (Nat × Nat × Nat) := [(5519333376,109502301198314,109502687079219)]
theorem point_links_checked42079 : (cuts42079.take 1).map (fun c => (5519310849-1+2*2^10*c.k,109502247089339+c.lower,109502632970216+c.upper)) = pointBounds42079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000064
