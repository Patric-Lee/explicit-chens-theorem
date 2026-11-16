import PlattAssemblyKernel
import PlattCertificates.Count131072.C073136
import PlattCertificates.Count131072.C073137
import PlattCertificates.Count131072.C073138
import PlattCertificates.Count131072.C073139
import PlattCertificates.Count131072.C073140
import PlattCertificates.Count131072.C073141
import PlattCertificates.Count131072.C073142
import PlattCertificates.Count131072.C073143
import PlattCertificates.Count131072.C073144
import PlattCertificates.Count131072.C073145
import PlattCertificates.Count131072.C073146
import PlattCertificates.Count131072.C073147
import PlattCertificates.Count131072.C073148
import PlattCertificates.Count131072.C073149
import PlattCertificates.Count131072.C073150
import PlattCertificates.Count131072.C073151
import PlattCertificates.Count131072.C073152
import PlattCertificates.Count131072.C073153
import PlattCertificates.Count131072.C073154
import PlattCertificates.Count131072.C073155
import PlattCertificates.Count131072.C073156
import PlattCertificates.Count131072.C073157
import PlattCertificates.Count131072.C073158
import PlattCertificates.Count131072.C073159
import PlattCertificates.Count131072.C073160
import PlattCertificates.Count131072.C073161
import PlattCertificates.Count131072.C073162
import PlattCertificates.Count131072.C073163
import PlattCertificates.Count131072.C073164
import PlattCertificates.Count131072.C073165
import PlattCertificates.Count131072.C073166
import PlattCertificates.Count131072.C073167
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000098
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73136 : List PrefixCut := [⟨64,168531324,168531425⟩]
theorem checked73136 : checkPrefixCuts (2^48) 9590013953 10 Manual.Count131072.C073136.packed 64 cuts73136 = true := by
 decide +kernel
def cuts73137 : List PrefixCut := [⟨64,166386453,166386552⟩]
theorem checked73137 : checkPrefixCuts (2^48) 9590145025 10 Manual.Count131072.C073137.packed 64 cuts73137 = true := by
 decide +kernel
def cuts73138 : List PrefixCut := [⟨11,27677045,27677064⟩,
⟨64,168379960,168380062⟩]
theorem checked73138 : checkPrefixCuts (2^48) 9590276097 10 Manual.Count131072.C073138.packed 64 cuts73138 = true := by
 decide +kernel
def pointBounds73138 : List (Nat × Nat × Nat) := [(9590298624,116351111930798,116351501754367)]
theorem point_links_checked73138 : (cuts73138.take 1).map (fun c => (9590276097-1+2*2^10*c.k,116351084253753+c.lower,116351474077303+c.upper)) = pointBounds73138 := by
 decide +kernel
def cuts73139 : List PrefixCut := [⟨64,167409136,167409238⟩]
theorem checked73139 : checkPrefixCuts (2^48) 9590407169 10 Manual.Count131072.C073139.packed 64 cuts73139 = true := by
 decide +kernel
def cuts73140 : List PrefixCut := [⟨30,76571891,76571940⟩,
⟨64,166174185,166174285⟩]
theorem checked73140 : checkPrefixCuts (2^48) 9590538241 10 Manual.Count131072.C073140.packed 64 cuts73140 = true := by
 decide +kernel
def pointBounds73140 : List (Nat × Nat × Nat) := [(9590599680,116351496614740,116351886438543)]
theorem point_links_checked73140 : (cuts73140.take 1).map (fun c => (9590538241-1+2*2^10*c.k,116351420042849+c.lower,116351809866603+c.upper)) = pointBounds73140 := by
 decide +kernel
def cuts73141 : List PrefixCut := [⟨64,168578523,168578623⟩]
theorem checked73141 : checkPrefixCuts (2^48) 9590669313 10 Manual.Count131072.C073141.packed 64 cuts73141 = true := by
 decide +kernel
def cuts73142 : List PrefixCut := [⟨49,128193261,128193339⟩,
⟨64,167695764,167695869⟩]
theorem checked73142 : checkPrefixCuts (2^48) 9590800385 10 Manual.Count131072.C073142.packed 64 cuts73142 = true := by
 decide +kernel
def pointBounds73142 : List (Nat × Nat × Nat) := [(9590900736,116351882988818,116352272812850)]
theorem point_links_checked73142 : (cuts73142.take 1).map (fun c => (9590800385-1+2*2^10*c.k,116351754795557+c.lower,116352144619511+c.upper)) = pointBounds73142 := by
 decide +kernel
def cuts73143 : List PrefixCut := [⟨64,167429333,167429436⟩]
theorem checked73143 : checkPrefixCuts (2^48) 9590931457 10 Manual.Count131072.C073143.packed 64 cuts73143 = true := by
 decide +kernel
def cuts73144 : List PrefixCut := [⟨64,167485734,167485840⟩]
theorem checked73144 : checkPrefixCuts (2^48) 9591062529 10 Manual.Count131072.C073144.packed 64 cuts73144 = true := by
 decide +kernel
def cuts73145 : List PrefixCut := [⟨4,9919357,9919363⟩,
⟨64,166368265,166368360⟩]
theorem checked73145 : checkPrefixCuts (2^48) 9591193601 10 Manual.Count131072.C073145.packed 64 cuts73145 = true := by
 decide +kernel
def pointBounds73145 : List (Nat × Nat × Nat) := [(9591201792,116352267325745,116352657150019)]
theorem point_links_checked73145 : (cuts73145.take 1).map (fun c => (9591193601-1+2*2^10*c.k,116352257406388+c.lower,116352647230656+c.upper)) = pointBounds73145 := by
 decide +kernel
def cuts73146 : List PrefixCut := [⟨64,166542075,166542171⟩]
theorem checked73146 : checkPrefixCuts (2^48) 9591324673 10 Manual.Count131072.C073146.packed 64 cuts73146 = true := by
 decide +kernel
def cuts73147 : List PrefixCut := [⟨23,60541517,60541554⟩,
⟨64,168329917,168330022⟩]
theorem checked73147 : checkPrefixCuts (2^48) 9591455745 10 Manual.Count131072.C073147.packed 64 cuts73147 = true := by
 decide +kernel
def pointBounds73147 : List (Nat × Nat × Nat) := [(9591502848,116352650858245,116353040682741)]
theorem point_links_checked73147 : (cuts73147.take 1).map (fun c => (9591455745-1+2*2^10*c.k,116352590316728+c.lower,116352980141187+c.upper)) = pointBounds73147 := by
 decide +kernel
def cuts73148 : List PrefixCut := [⟨64,166038639,166038742⟩]
theorem checked73148 : checkPrefixCuts (2^48) 9591586817 10 Manual.Count131072.C073148.packed 64 cuts73148 = true := by
 decide +kernel
def cuts73149 : List PrefixCut := [⟨42,112099761,112099828⟩,
⟨64,170526226,170526327⟩]
theorem checked73149 : checkPrefixCuts (2^48) 9591717889 10 Manual.Count131072.C073149.packed 64 cuts73149 = true := by
 decide +kernel
def pointBounds73149 : List (Nat × Nat × Nat) := [(9591803904,116353036785045,116353426609779)]
theorem point_links_checked73149 : (cuts73149.take 1).map (fun c => (9591717889-1+2*2^10*c.k,116352924685284+c.lower,116353314509951+c.upper)) = pointBounds73149 := by
 decide +kernel
def cuts73150 : List PrefixCut := [⟨64,167295958,167296057⟩]
theorem checked73150 : checkPrefixCuts (2^48) 9591848961 10 Manual.Count131072.C073150.packed 64 cuts73150 = true := by
 decide +kernel
def cuts73151 : List PrefixCut := [⟨61,158989175,158989268⟩,
⟨64,166149215,166149312⟩]
theorem checked73151 : checkPrefixCuts (2^48) 9591980033 10 Manual.Count131072.C073151.packed 64 cuts73151 = true := by
 decide +kernel
def pointBounds73151 : List (Nat × Nat × Nat) := [(9592104960,116353421496643,116353811321603)]
theorem point_links_checked73151 : (cuts73151.take 1).map (fun c => (9591980033-1+2*2^10*c.k,116353262507468+c.lower,116353652332335+c.upper)) = pointBounds73151 := by
 decide +kernel
def cuts73152 : List PrefixCut := [⟨64,167790218,167790320⟩]
theorem checked73152 : checkPrefixCuts (2^48) 9592111105 10 Manual.Count131072.C073152.packed 64 cuts73152 = true := by
 decide +kernel
def cuts73153 : List PrefixCut := [⟨64,166790237,166790332⟩]
theorem checked73153 : checkPrefixCuts (2^48) 9592242177 10 Manual.Count131072.C073153.packed 64 cuts73153 = true := by
 decide +kernel
def cuts73154 : List PrefixCut := [⟨16,42606853,42606878⟩,
⟨64,166435848,166435947⟩]
theorem checked73154 : checkPrefixCuts (2^48) 9592373249 10 Manual.Count131072.C073154.packed 64 cuts73154 = true := by
 decide +kernel
def pointBounds73154 : List (Nat × Nat × Nat) := [(9592406016,116353805843991,116354195669177)]
theorem point_links_checked73154 : (cuts73154.take 1).map (fun c => (9592373249-1+2*2^10*c.k,116353763237138+c.lower,116354153062299+c.upper)) = pointBounds73154 := by
 decide +kernel
def cuts73155 : List PrefixCut := [⟨64,167137806,167137901⟩]
theorem checked73155 : checkPrefixCuts (2^48) 9592504321 10 Manual.Count131072.C073155.packed 64 cuts73155 = true := by
 decide +kernel
def cuts73156 : List PrefixCut := [⟨35,91725286,91725338⟩,
⟨64,167399595,167399697⟩]
theorem checked73156 : checkPrefixCuts (2^48) 9592635393 10 Manual.Count131072.C073156.packed 64 cuts73156 = true := by
 decide +kernel
def pointBounds73156 : List (Nat × Nat × Nat) := [(9592707072,116354188536078,116354578361485)]
theorem point_links_checked73156 : (cuts73156.take 1).map (fun c => (9592635393-1+2*2^10*c.k,116354096810792+c.lower,116354486636147+c.upper)) = pointBounds73156 := by
 decide +kernel
def cuts73157 : List PrefixCut := [⟨64,165636791,165636889⟩]
theorem checked73157 : checkPrefixCuts (2^48) 9592766465 10 Manual.Count131072.C073157.packed 64 cuts73157 = true := by
 decide +kernel
def cuts73158 : List PrefixCut := [⟨54,141721095,141721178⟩,
⟨64,168392646,168392744⟩]
theorem checked73158 : checkPrefixCuts (2^48) 9592897537 10 Manual.Count131072.C073158.packed 64 cuts73158 = true := by
 decide +kernel
def pointBounds73158 : List (Nat × Nat × Nat) := [(9593008128,116354571568273,116354961393911)]
theorem point_links_checked73158 : (cuts73158.take 1).map (fun c => (9592897537-1+2*2^10*c.k,116354429847178+c.lower,116354819672733+c.upper)) = pointBounds73158 := by
 decide +kernel
def cuts73159 : List PrefixCut := [⟨64,168478372,168478470⟩]
theorem checked73159 : checkPrefixCuts (2^48) 9593028609 10 Manual.Count131072.C073159.packed 64 cuts73159 = true := by
 decide +kernel
def cuts73160 : List PrefixCut := [⟨64,169121569,169121666⟩]
theorem checked73160 : checkPrefixCuts (2^48) 9593159681 10 Manual.Count131072.C073160.packed 64 cuts73160 = true := by
 decide +kernel
def cuts73161 : List PrefixCut := [⟨9,23971419,23971429⟩,
⟨64,169970142,169970236⟩]
theorem checked73161 : checkPrefixCuts (2^48) 9593290753 10 Manual.Count131072.C073161.packed 64 cuts73161 = true := by
 decide +kernel
def pointBounds73161 : List (Nat × Nat × Nat) := [(9593309184,116354959811184,116355349637042)]
theorem point_links_checked73161 : (cuts73161.take 1).map (fun c => (9593290753-1+2*2^10*c.k,116354935839765+c.lower,116355325665613+c.upper)) = pointBounds73161 := by
 decide +kernel
def cuts73162 : List PrefixCut := [⟨64,165742825,165742917⟩]
theorem checked73162 : checkPrefixCuts (2^48) 9593421825 10 Manual.Count131072.C073162.packed 64 cuts73162 = true := by
 decide +kernel
def cuts73163 : List PrefixCut := [⟨28,72851018,72851059⟩,
⟨64,167295570,167295658⟩]
theorem checked73163 : checkPrefixCuts (2^48) 9593552897 10 Manual.Count131072.C073163.packed 64 cuts73163 = true := by
 decide +kernel
def pointBounds73163 : List (Nat × Nat × Nat) := [(9593610240,116355344403750,116355734229825)]
theorem point_links_checked73163 : (cuts73163.take 1).map (fun c => (9593552897-1+2*2^10*c.k,116355271552732+c.lower,116355661378766+c.upper)) = pointBounds73163 := by
 decide +kernel
def cuts73164 : List PrefixCut := [⟨64,168701568,168701666⟩]
theorem checked73164 : checkPrefixCuts (2^48) 9593683969 10 Manual.Count131072.C073164.packed 64 cuts73164 = true := by
 decide +kernel
def cuts73165 : List PrefixCut := [⟨47,123077341,123077417⟩,
⟨64,167437691,167437795⟩]
theorem checked73165 : checkPrefixCuts (2^48) 9593815041 10 Manual.Count131072.C073165.packed 64 cuts73165 = true := by
 decide +kernel
def pointBounds73165 : List (Nat × Nat × Nat) := [(9593911296,116355730627211,116356120453507)]
theorem point_links_checked73165 : (cuts73165.take 1).map (fun c => (9593815041-1+2*2^10*c.k,116355607549870+c.lower,116355997376090+c.upper)) = pointBounds73165 := by
 decide +kernel
def cuts73166 : List PrefixCut := [⟨64,165968468,165968568⟩]
theorem checked73166 : checkPrefixCuts (2^48) 9593946113 10 Manual.Count131072.C073166.packed 64 cuts73166 = true := by
 decide +kernel
def cuts73167 : List PrefixCut := [⟨64,168342611,168342711⟩]
theorem checked73167 : checkPrefixCuts (2^48) 9594077185 10 Manual.Count131072.C073167.packed 64 cuts73167 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000098
