import PlattAssemblyKernel
import PlattCertificates.Count131072.C071152
import PlattCertificates.Count131072.C071153
import PlattCertificates.Count131072.C071154
import PlattCertificates.Count131072.C071155
import PlattCertificates.Count131072.C071156
import PlattCertificates.Count131072.C071157
import PlattCertificates.Count131072.C071158
import PlattCertificates.Count131072.C071159
import PlattCertificates.Count131072.C071160
import PlattCertificates.Count131072.C071161
import PlattCertificates.Count131072.C071162
import PlattCertificates.Count131072.C071163
import PlattCertificates.Count131072.C071164
import PlattCertificates.Count131072.C071165
import PlattCertificates.Count131072.C071166
import PlattCertificates.Count131072.C071167
import PlattCertificates.Count131072.C071168
import PlattCertificates.Count131072.C071169
import PlattCertificates.Count131072.C071170
import PlattCertificates.Count131072.C071171
import PlattCertificates.Count131072.C071172
import PlattCertificates.Count131072.C071173
import PlattCertificates.Count131072.C071174
import PlattCertificates.Count131072.C071175
import PlattCertificates.Count131072.C071176
import PlattCertificates.Count131072.C071177
import PlattCertificates.Count131072.C071178
import PlattCertificates.Count131072.C071179
import PlattCertificates.Count131072.C071180
import PlattCertificates.Count131072.C071181
import PlattCertificates.Count131072.C071182
import PlattCertificates.Count131072.C071183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71152 : List PrefixCut := [⟨64,173530329,173530435⟩]
theorem checked71152 : checkPrefixCuts (2^48) 9329967105 10 Manual.Count131072.C071152.packed 64 cuts71152 = true := by
 decide +kernel
def cuts71153 : List PrefixCut := [⟨28,75601986,75602028⟩,
⟨64,174432935,174433032⟩]
theorem checked71153 : checkPrefixCuts (2^48) 9330098177 10 Manual.Count131072.C071153.packed 64 cuts71153 = true := by
 decide +kernel
def pointBounds71153 : List (Nat × Nat × Nat) := [(9330155520,116014152928528,116014542551915)]
theorem point_links_checked71153 : (cuts71153.take 1).map (fun c => (9330098177-1+2*2^10*c.k,116014077326542+c.lower,116014466949887+c.upper)) = pointBounds71153 := by
 decide +kernel
def cuts71154 : List PrefixCut := [⟨64,173434960,173435056⟩]
theorem checked71154 : checkPrefixCuts (2^48) 9330229249 10 Manual.Count131072.C071154.packed 64 cuts71154 = true := by
 decide +kernel
def cuts71155 : List PrefixCut := [⟨43,117894549,117894624⟩,
⟨64,173885019,173885127⟩]
theorem checked71155 : checkPrefixCuts (2^48) 9330360321 10 Manual.Count131072.C071155.packed 64 cuts71155 = true := by
 decide +kernel
def pointBounds71155 : List (Nat × Nat × Nat) := [(9330448384,116014543088986,116014932712599)]
theorem point_links_checked71155 : (cuts71155.take 1).map (fun c => (9330360321-1+2*2^10*c.k,116014425194437+c.lower,116014814817975+c.upper)) = pointBounds71155 := by
 decide +kernel
def cuts71156 : List PrefixCut := [⟨64,172826736,172826839⟩]
theorem checked71156 : checkPrefixCuts (2^48) 9330491393 10 Manual.Count131072.C071156.packed 64 cuts71156 = true := by
 decide +kernel
def cuts71157 : List PrefixCut := [⟨58,157801456,157801546⟩,
⟨64,173699140,173699240⟩]
theorem checked71157 : checkPrefixCuts (2^48) 9330622465 10 Manual.Count131072.C071157.packed 64 cuts71157 = true := by
 decide +kernel
def pointBounds71157 : List (Nat × Nat × Nat) := [(9330741248,116014929707648,116015319331487)]
theorem point_links_checked71157 : (cuts71157.take 1).map (fun c => (9330622465-1+2*2^10*c.k,116014771906192+c.lower,116015161529941+c.upper)) = pointBounds71157 := by
 decide +kernel
def cuts71158 : List PrefixCut := [⟨64,169895759,169895862⟩]
theorem checked71158 : checkPrefixCuts (2^48) 9330753537 10 Manual.Count131072.C071158.packed 64 cuts71158 = true := by
 decide +kernel
def cuts71159 : List PrefixCut := [⟨64,173121092,173121199⟩]
theorem checked71159 : checkPrefixCuts (2^48) 9330884609 10 Manual.Count131072.C071159.packed 64 cuts71159 = true := by
 decide +kernel
def cuts71160 : List PrefixCut := [⟨9,24041892,24041908⟩,
⟨64,173178989,173179094⟩]
theorem checked71160 : checkPrefixCuts (2^48) 9331015681 10 Manual.Count131072.C071160.packed 64 cuts71160 = true := by
 decide +kernel
def pointBounds71160 : List (Nat × Nat × Nat) := [(9331034112,116015312664075,116015702288150)]
theorem point_links_checked71160 : (cuts71160.take 1).map (fun c => (9331015681-1+2*2^10*c.k,116015288622183+c.lower,116015678246242+c.upper)) = pointBounds71160 := by
 decide +kernel
def cuts71161 : List PrefixCut := [⟨64,172603438,172603536⟩]
theorem checked71161 : checkPrefixCuts (2^48) 9331146753 10 Manual.Count131072.C071161.packed 64 cuts71161 = true := by
 decide +kernel
def cuts71162 : List PrefixCut := [⟨24,65577813,65577849⟩,
⟨64,174622027,174622130⟩]
theorem checked71162 : checkPrefixCuts (2^48) 9331277825 10 Manual.Count131072.C071162.packed 64 cuts71162 = true := by
 decide +kernel
def pointBounds71162 : List (Nat × Nat × Nat) := [(9331326976,116015699982423,116016089606721)]
theorem point_links_checked71162 : (cuts71162.take 1).map (fun c => (9331277825-1+2*2^10*c.k,116015634404610+c.lower,116016024028872+c.upper)) = pointBounds71162 := by
 decide +kernel
def cuts71163 : List PrefixCut := [⟨64,172598588,172598689⟩]
theorem checked71163 : checkPrefixCuts (2^48) 9331408897 10 Manual.Count131072.C071163.packed 64 cuts71163 = true := by
 decide +kernel
def cuts71164 : List PrefixCut := [⟨39,103763095,103763158⟩,
⟨64,170303735,170303832⟩]
theorem checked71164 : checkPrefixCuts (2^48) 9331539969 10 Manual.Count131072.C071164.packed 64 cuts71164 = true := by
 decide +kernel
def pointBounds71164 : List (Nat × Nat × Nat) := [(9331619840,116016085388320,116016475012849)]
theorem point_links_checked71164 : (cuts71164.take 1).map (fun c => (9331539969-1+2*2^10*c.k,116015981625225+c.lower,116016371249691+c.upper)) = pointBounds71164 := by
 decide +kernel
def cuts71165 : List PrefixCut := [⟨64,174916312,174916421⟩]
theorem checked71165 : checkPrefixCuts (2^48) 9331671041 10 Manual.Count131072.C071165.packed 64 cuts71165 = true := by
 decide +kernel
def cuts71166 : List PrefixCut := [⟨54,144932229,144932313⟩,
⟨64,171626114,171626213⟩]
theorem checked71166 : checkPrefixCuts (2^48) 9331802113 10 Manual.Count131072.C071166.packed 64 cuts71166 = true := by
 decide +kernel
def pointBounds71166 : List (Nat × Nat × Nat) := [(9331912704,116016471777501,116016861402257)]
theorem point_links_checked71166 : (cuts71166.take 1).map (fun c => (9331802113-1+2*2^10*c.k,116016326845272+c.lower,116016716469944+c.upper)) = pointBounds71166 := by
 decide +kernel
def cuts71167 : List PrefixCut := [⟨64,173252456,173252560⟩]
theorem checked71167 : checkPrefixCuts (2^48) 9331933185 10 Manual.Count131072.C071167.packed 64 cuts71167 = true := by
 decide +kernel
def cuts71168 : List PrefixCut := [⟨64,172284852,172284949⟩]
theorem checked71168 : checkPrefixCuts (2^48) 9332064257 10 Manual.Count131072.C071168.packed 64 cuts71168 = true := by
 decide +kernel
def cuts71169 : List PrefixCut := [⟨5,14115669,14115676⟩,
⟨64,174393740,174393838⟩]
theorem checked71169 : checkPrefixCuts (2^48) 9332195329 10 Manual.Count131072.C071169.packed 64 cuts71169 = true := by
 decide +kernel
def pointBounds71169 : List (Nat × Nat × Nat) := [(9332205568,116016858124363,116017247749342)]
theorem point_links_checked71169 : (cuts71169.take 1).map (fun c => (9332195329-1+2*2^10*c.k,116016844008694+c.lower,116017233633666+c.upper)) = pointBounds71169 := by
 decide +kernel
def cuts71170 : List PrefixCut := [⟨64,173275332,173275439⟩]
theorem checked71170 : checkPrefixCuts (2^48) 9332326401 10 Manual.Count131072.C071170.packed 64 cuts71170 = true := by
 decide +kernel
def cuts71171 : List PrefixCut := [⟨20,53143305,53143338⟩,
⟨64,172699830,172699933⟩]
theorem checked71171 : checkPrefixCuts (2^48) 9332457473 10 Manual.Count131072.C071171.packed 64 cuts71171 = true := by
 decide +kernel
def pointBounds71171 : List (Nat × Nat × Nat) := [(9332498432,116017244821071,116017634446281)]
theorem point_links_checked71171 : (cuts71171.take 1).map (fun c => (9332457473-1+2*2^10*c.k,116017191677766+c.lower,116017581302943+c.upper)) = pointBounds71171 := by
 decide +kernel
def cuts71172 : List PrefixCut := [⟨64,171732283,171732395⟩]
theorem checked71172 : checkPrefixCuts (2^48) 9332588545 10 Manual.Count131072.C071172.packed 64 cuts71172 = true := by
 decide +kernel
def cuts71173 : List PrefixCut := [⟨35,93857585,93857641⟩,
⟨64,170583808,170583917⟩]
theorem checked71173 : checkPrefixCuts (2^48) 9332719617 10 Manual.Count131072.C071173.packed 64 cuts71173 = true := by
 decide +kernel
def pointBounds71173 : List (Nat × Nat × Nat) := [(9332791296,116017629967464,116018019592912)]
theorem point_links_checked71173 : (cuts71173.take 1).map (fun c => (9332719617-1+2*2^10*c.k,116017536109879+c.lower,116017925735271+c.upper)) = pointBounds71173 := by
 decide +kernel
def cuts71174 : List PrefixCut := [⟨64,171486191,171486297⟩]
theorem checked71174 : checkPrefixCuts (2^48) 9332850689 10 Manual.Count131072.C071174.packed 64 cuts71174 = true := by
 decide +kernel
def cuts71175 : List PrefixCut := [⟨50,132820211,132820289⟩,
⟨64,171453611,171453714⟩]
theorem checked71175 : checkPrefixCuts (2^48) 9332981761 10 Manual.Count131072.C071175.packed 64 cuts71175 = true := by
 decide +kernel
def pointBounds71175 : List (Nat × Nat × Nat) := [(9333084160,116018011000089,116018400625774)]
theorem point_links_checked71175 : (cuts71175.take 1).map (fun c => (9332981761-1+2*2^10*c.k,116017878179878+c.lower,116018267805485+c.upper)) = pointBounds71175 := by
 decide +kernel
def cuts71176 : List PrefixCut := [⟨64,171028990,171029094⟩]
theorem checked71176 : checkPrefixCuts (2^48) 9333112833 10 Manual.Count131072.C071176.packed 64 cuts71176 = true := by
 decide +kernel
def cuts71177 : List PrefixCut := [⟨64,171629757,171629855⟩]
theorem checked71177 : checkPrefixCuts (2^48) 9333243905 10 Manual.Count131072.C071177.packed 64 cuts71177 = true := by
 decide +kernel
def cuts71178 : List PrefixCut := [⟨1,2593578,2593580⟩,
⟨64,172984443,172984541⟩]
theorem checked71178 : checkPrefixCuts (2^48) 9333374977 10 Manual.Count131072.C071178.packed 64 cuts71178 = true := by
 decide +kernel
def pointBounds71178 : List (Nat × Nat × Nat) := [(9333377024,116018394885814,116018784511728)]
theorem point_links_checked71178 : (cuts71178.take 1).map (fun c => (9333374977-1+2*2^10*c.k,116018392292236+c.lower,116018781918148+c.upper)) = pointBounds71178 := by
 decide +kernel
def cuts71179 : List PrefixCut := [⟨64,171263046,171263151⟩]
theorem checked71179 : checkPrefixCuts (2^48) 9333506049 10 Manual.Count131072.C071179.packed 64 cuts71179 = true := by
 decide +kernel
def cuts71180 : List PrefixCut := [⟨16,42822924,42822951⟩,
⟨64,170717824,170717925⟩]
theorem checked71180 : checkPrefixCuts (2^48) 9333637121 10 Manual.Count131072.C071180.packed 64 cuts71180 = true := by
 decide +kernel
def pointBounds71180 : List (Nat × Nat × Nat) := [(9333669888,116018779362649,116019168988791)]
theorem point_links_checked71180 : (cuts71180.take 1).map (fun c => (9333637121-1+2*2^10*c.k,116018736539725+c.lower,116019126165840+c.upper)) = pointBounds71180 := by
 decide +kernel
def cuts71181 : List PrefixCut := [⟨64,172916851,172916956⟩]
theorem checked71181 : checkPrefixCuts (2^48) 9333768193 10 Manual.Count131072.C071181.packed 64 cuts71181 = true := by
 decide +kernel
def cuts71182 : List PrefixCut := [⟨31,82265820,82265870⟩,
⟨64,169024293,169024397⟩]
theorem checked71182 : checkPrefixCuts (2^48) 9333899265 10 Manual.Count131072.C071182.packed 64 cuts71182 = true := by
 decide +kernel
def pointBounds71182 : List (Nat × Nat × Nat) := [(9333962752,116019162440220,116019552066591)]
theorem point_links_checked71182 : (cuts71182.take 1).map (fun c => (9333899265-1+2*2^10*c.k,116019080174400+c.lower,116019469800721+c.upper)) = pointBounds71182 := by
 decide +kernel
def cuts71183 : List PrefixCut := [⟨64,172670741,172670843⟩]
theorem checked71183 : checkPrefixCuts (2^48) 9334030337 10 Manual.Count131072.C071183.packed 64 cuts71183 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000036
