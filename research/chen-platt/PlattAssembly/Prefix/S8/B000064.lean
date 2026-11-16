import PlattAssemblyKernel
import PlattCertificates.Count131072.C072048
import PlattCertificates.Count131072.C072049
import PlattCertificates.Count131072.C072050
import PlattCertificates.Count131072.C072051
import PlattCertificates.Count131072.C072052
import PlattCertificates.Count131072.C072053
import PlattCertificates.Count131072.C072054
import PlattCertificates.Count131072.C072055
import PlattCertificates.Count131072.C072056
import PlattCertificates.Count131072.C072057
import PlattCertificates.Count131072.C072058
import PlattCertificates.Count131072.C072059
import PlattCertificates.Count131072.C072060
import PlattCertificates.Count131072.C072061
import PlattCertificates.Count131072.C072062
import PlattCertificates.Count131072.C072063
import PlattCertificates.Count131072.C072064
import PlattCertificates.Count131072.C072065
import PlattCertificates.Count131072.C072066
import PlattCertificates.Count131072.C072067
import PlattCertificates.Count131072.C072068
import PlattCertificates.Count131072.C072069
import PlattCertificates.Count131072.C072070
import PlattCertificates.Count131072.C072071
import PlattCertificates.Count131072.C072072
import PlattCertificates.Count131072.C072073
import PlattCertificates.Count131072.C072074
import PlattCertificates.Count131072.C072075
import PlattCertificates.Count131072.C072076
import PlattCertificates.Count131072.C072077
import PlattCertificates.Count131072.C072078
import PlattCertificates.Count131072.C072079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72048 : List PrefixCut := [⟨64,167529793,167529891⟩]
theorem checked72048 : checkPrefixCuts (2^48) 9447407617 10 Manual.Count131072.C072048.packed 64 cuts72048 = true := by
 decide +kernel
def cuts72049 : List PrefixCut := [⟨32,86460332,86460381⟩,
⟨64,170208884,170208982⟩]
theorem checked72049 : checkPrefixCuts (2^48) 9447538689 10 Manual.Count131072.C072049.packed 64 cuts72049 = true := by
 decide +kernel
def pointBounds72049 : List (Nat × Nat × Nat) := [(9447604224,116167477619939,116167867334137)]
theorem point_links_checked72049 : (cuts72049.take 1).map (fun c => (9447538689-1+2*2^10*c.k,116167391159607+c.lower,116167780873756+c.upper)) = pointBounds72049 := by
 decide +kernel
def cuts72050 : List PrefixCut := [⟨64,172977256,172977360⟩]
theorem checked72050 : checkPrefixCuts (2^48) 9447669761 10 Manual.Count131072.C072050.packed 64 cuts72050 = true := by
 decide +kernel
def cuts72051 : List PrefixCut := [⟨49,131146492,131146568⟩,
⟨64,171187304,171187405⟩]
theorem checked72051 : checkPrefixCuts (2^48) 9447800833 10 Manual.Count131072.C072051.packed 64 cuts72051 = true := by
 decide +kernel
def pointBounds72051 : List (Nat × Nat × Nat) := [(9447901184,116167865492239,116168255206666)]
theorem point_links_checked72051 : (cuts72051.take 1).map (fun c => (9447800833-1+2*2^10*c.k,116167734345747+c.lower,116168124060098+c.upper)) = pointBounds72051 := by
 decide +kernel
def cuts72052 : List PrefixCut := [⟨64,169427192,169427296⟩]
theorem checked72052 : checkPrefixCuts (2^48) 9447931905 10 Manual.Count131072.C072052.packed 64 cuts72052 = true := by
 decide +kernel
def cuts72053 : List PrefixCut := [⟨64,172433791,172433893⟩]
theorem checked72053 : checkPrefixCuts (2^48) 9448062977 10 Manual.Count131072.C072053.packed 64 cuts72053 = true := by
 decide +kernel
def cuts72054 : List PrefixCut := [⟨2,5660364,5660367⟩,
⟨64,171001429,171001523⟩]
theorem checked72054 : checkPrefixCuts (2^48) 9448194049 10 Manual.Count131072.C072054.packed 64 cuts72054 = true := by
 decide +kernel
def pointBounds72054 : List (Nat × Nat × Nat) := [(9448198144,116168253054398,116168642769059)]
theorem point_links_checked72054 : (cuts72054.take 1).map (fun c => (9448194049-1+2*2^10*c.k,116168247394034+c.lower,116168637108692+c.upper)) = pointBounds72054 := by
 decide +kernel
def cuts72055 : List PrefixCut := [⟨64,168973291,168973389⟩]
theorem checked72055 : checkPrefixCuts (2^48) 9448325121 10 Manual.Count131072.C072055.packed 64 cuts72055 = true := by
 decide +kernel
def cuts72056 : List PrefixCut := [⟨19,49630991,49631018⟩,
⟨64,167600584,167600683⟩]
theorem checked72056 : checkPrefixCuts (2^48) 9448456193 10 Manual.Count131072.C072056.packed 64 cuts72056 = true := by
 decide +kernel
def pointBounds72056 : List (Nat × Nat × Nat) := [(9448495104,116168636999745,116169026714622)]
theorem point_links_checked72056 : (cuts72056.take 1).map (fun c => (9448456193-1+2*2^10*c.k,116168587368754+c.lower,116168977083604+c.upper)) = pointBounds72056 := by
 decide +kernel
def cuts72057 : List PrefixCut := [⟨64,171828437,171828535⟩]
theorem checked72057 : checkPrefixCuts (2^48) 9448587265 10 Manual.Count131072.C072057.packed 64 cuts72057 = true := by
 decide +kernel
def cuts72058 : List PrefixCut := [⟨36,95803441,95803499⟩,
⟨64,169025835,169025938⟩]
theorem checked72058 : checkPrefixCuts (2^48) 9448718337 10 Manual.Count131072.C072058.packed 64 cuts72058 = true := by
 decide +kernel
def pointBounds72058 : List (Nat × Nat × Nat) := [(9448792064,116169022601216,116169412316321)]
theorem point_links_checked72058 : (cuts72058.take 1).map (fun c => (9448718337-1+2*2^10*c.k,116168926797775+c.lower,116169316512822+c.upper)) = pointBounds72058 := by
 decide +kernel
def cuts72059 : List PrefixCut := [⟨64,170929995,170930097⟩]
theorem checked72059 : checkPrefixCuts (2^48) 9448849409 10 Manual.Count131072.C072059.packed 64 cuts72059 = true := by
 decide +kernel
def cuts72060 : List PrefixCut := [⟨53,143283874,143283964⟩,
⟨64,173161778,173161887⟩]
theorem checked72060 : checkPrefixCuts (2^48) 9448980481 10 Manual.Count131072.C072060.packed 64 cuts72060 = true := by
 decide +kernel
def pointBounds72060 : List (Nat × Nat × Nat) := [(9449089024,116169410037479,116169799752821)]
theorem point_links_checked72060 : (cuts72060.take 1).map (fun c => (9448980481-1+2*2^10*c.k,116169266753605+c.lower,116169656468857+c.upper)) = pointBounds72060 := by
 decide +kernel
def cuts72061 : List PrefixCut := [⟨64,169078369,169078467⟩]
theorem checked72061 : checkPrefixCuts (2^48) 9449111553 10 Manual.Count131072.C072061.packed 64 cuts72061 = true := by
 decide +kernel
def cuts72062 : List PrefixCut := [⟨64,170029239,170029338⟩]
theorem checked72062 : checkPrefixCuts (2^48) 9449242625 10 Manual.Count131072.C072062.packed 64 cuts72062 = true := by
 decide +kernel
def cuts72063 : List PrefixCut := [⟨6,15847033,15847043⟩,
⟨64,170652420,170652523⟩]
theorem checked72063 : checkPrefixCuts (2^48) 9449373697 10 Manual.Count131072.C072063.packed 64 cuts72063 = true := by
 decide +kernel
def pointBounds72063 : List (Nat × Nat × Nat) := [(9449385984,116169794870024,116170184585592)]
theorem point_links_checked72063 : (cuts72063.take 1).map (fun c => (9449373697-1+2*2^10*c.k,116169779022991+c.lower,116170168738549+c.upper)) = pointBounds72063 := by
 decide +kernel
def cuts72064 : List PrefixCut := [⟨64,172437272,172437381⟩]
theorem checked72064 : checkPrefixCuts (2^48) 9449504769 10 Manual.Count131072.C072064.packed 64 cuts72064 = true := by
 decide +kernel
def cuts72065 : List PrefixCut := [⟨23,61092681,61092717⟩,
⟨64,168949844,168949944⟩]
theorem checked72065 : checkPrefixCuts (2^48) 9449635841 10 Manual.Count131072.C072065.packed 64 cuts72065 = true := by
 decide +kernel
def pointBounds72065 : List (Nat × Nat × Nat) := [(9449682944,116170183205364,116170572921170)]
theorem point_links_checked72065 : (cuts72065.take 1).map (fun c => (9449635841-1+2*2^10*c.k,116170122112683+c.lower,116170511828453+c.upper)) = pointBounds72065 := by
 decide +kernel
def cuts72066 : List PrefixCut := [⟨64,168977292,168977391⟩]
theorem checked72066 : checkPrefixCuts (2^48) 9449766913 10 Manual.Count131072.C072066.packed 64 cuts72066 = true := by
 decide +kernel
def cuts72067 : List PrefixCut := [⟨40,106186717,106186780⟩,
⟨64,170434450,170434550⟩]
theorem checked72067 : checkPrefixCuts (2^48) 9449897985 10 Manual.Count131072.C072067.packed 64 cuts72067 = true := by
 decide +kernel
def pointBounds72067 : List (Nat × Nat × Nat) := [(9449979904,116170566226536,116170955942568)]
theorem point_links_checked72067 : (cuts72067.take 1).map (fun c => (9449897985-1+2*2^10*c.k,116170460039819+c.lower,116170849755788+c.upper)) = pointBounds72067 := by
 decide +kernel
def cuts72068 : List PrefixCut := [⟨64,172546847,172546948⟩]
theorem checked72068 : checkPrefixCuts (2^48) 9450029057 10 Manual.Count131072.C072068.packed 64 cuts72068 = true := by
 decide +kernel
def cuts72069 : List PrefixCut := [⟨57,149997338,149997418⟩,
⟨64,168255426,168255517⟩]
theorem checked72069 : checkPrefixCuts (2^48) 9450160129 10 Manual.Count131072.C072069.packed 64 cuts72069 = true := by
 decide +kernel
def pointBounds72069 : List (Nat × Nat × Nat) := [(9450276864,116170953018454,116171342734704)]
theorem point_links_checked72069 : (cuts72069.take 1).map (fun c => (9450160129-1+2*2^10*c.k,116170803021116+c.lower,116171192737286+c.upper)) = pointBounds72069 := by
 decide +kernel
def cuts72070 : List PrefixCut := [⟨64,171708092,171708197⟩]
theorem checked72070 : checkPrefixCuts (2^48) 9450291201 10 Manual.Count131072.C072070.packed 64 cuts72070 = true := by
 decide +kernel
def cuts72071 : List PrefixCut := [⟨64,166910467,166910571⟩]
theorem checked72071 : checkPrefixCuts (2^48) 9450422273 10 Manual.Count131072.C072071.packed 64 cuts72071 = true := by
 decide +kernel
def cuts72072 : List PrefixCut := [⟨10,26358776,26358790⟩,
⟨64,168784518,168784618⟩]
theorem checked72072 : checkPrefixCuts (2^48) 9450553345 10 Manual.Count131072.C072072.packed 64 cuts72072 = true := by
 decide +kernel
def pointBounds72072 : List (Nat × Nat × Nat) := [(9450573824,116171336253877,116171725970361)]
theorem point_links_checked72072 : (cuts72072.take 1).map (fun c => (9450553345-1+2*2^10*c.k,116171309895101+c.lower,116171699611571+c.upper)) = pointBounds72072 := by
 decide +kernel
def cuts72073 : List PrefixCut := [⟨64,170986140,170986246⟩]
theorem checked72073 : checkPrefixCuts (2^48) 9450684417 10 Manual.Count131072.C072073.packed 64 cuts72073 = true := by
 decide +kernel
def cuts72074 : List PrefixCut := [⟨27,71241045,71241089⟩,
⟨64,168928755,168928860⟩]
theorem checked72074 : checkPrefixCuts (2^48) 9450815489 10 Manual.Count131072.C072074.packed 64 cuts72074 = true := by
 decide +kernel
def pointBounds72074 : List (Nat × Nat × Nat) := [(9450870784,116171720906804,116172110623524)]
theorem point_links_checked72074 : (cuts72074.take 1).map (fun c => (9450815489-1+2*2^10*c.k,116171649665759+c.lower,116172039382435+c.upper)) = pointBounds72074 := by
 decide +kernel
def cuts72075 : List PrefixCut := [⟨64,169998572,169998676⟩]
theorem checked72075 : checkPrefixCuts (2^48) 9450946561 10 Manual.Count131072.C072075.packed 64 cuts72075 = true := by
 decide +kernel
def cuts72076 : List PrefixCut := [⟨44,116894996,116895064⟩,
⟨64,170085572,170085670⟩]
theorem checked72076 : checkPrefixCuts (2^48) 9451077633 10 Manual.Count131072.C072076.packed 64 cuts72076 = true := by
 decide +kernel
def pointBounds72076 : List (Nat × Nat × Nat) := [(9451167744,116172105488082,116172495205035)]
theorem point_links_checked72076 : (cuts72076.take 1).map (fun c => (9451077633-1+2*2^10*c.k,116171988593086+c.lower,116172378309971+c.upper)) = pointBounds72076 := by
 decide +kernel
def cuts72077 : List PrefixCut := [⟨64,167760262,167760359⟩]
theorem checked72077 : checkPrefixCuts (2^48) 9451208705 10 Manual.Count131072.C072077.packed 64 cuts72077 = true := by
 decide +kernel
def cuts72078 : List PrefixCut := [⟨61,160312633,160312735⟩,
⟨64,168055713,168055820⟩]
theorem checked72078 : checkPrefixCuts (2^48) 9451339777 10 Manual.Count131072.C072078.packed 64 cuts72078 = true := by
 decide +kernel
def pointBounds72078 : List (Nat × Nat × Nat) := [(9451464704,116172486751553,116172876468735)]
theorem point_links_checked72078 : (cuts72078.take 1).map (fun c => (9451339777-1+2*2^10*c.k,116172326438920+c.lower,116172716156000+c.upper)) = pointBounds72078 := by
 decide +kernel
def cuts72079 : List PrefixCut := [⟨64,171061269,171061369⟩]
theorem checked72079 : checkPrefixCuts (2^48) 9451470849 10 Manual.Count131072.C072079.packed 64 cuts72079 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000064
