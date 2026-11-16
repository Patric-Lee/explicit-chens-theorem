import PlattAssemblyKernel
import PlattCertificates.Count131072.C048128
import PlattCertificates.Count131072.C048129
import PlattCertificates.Count131072.C048130
import PlattCertificates.Count131072.C048131
import PlattCertificates.Count131072.C048132
import PlattCertificates.Count131072.C048133
import PlattCertificates.Count131072.C048134
import PlattCertificates.Count131072.C048135
import PlattCertificates.Count131072.C048136
import PlattCertificates.Count131072.C048137
import PlattCertificates.Count131072.C048138
import PlattCertificates.Count131072.C048139
import PlattCertificates.Count131072.C048140
import PlattCertificates.Count131072.C048141
import PlattCertificates.Count131072.C048142
import PlattCertificates.Count131072.C048143
import PlattCertificates.Count131072.C048144
import PlattCertificates.Count131072.C048145
import PlattCertificates.Count131072.C048146
import PlattCertificates.Count131072.C048147
import PlattCertificates.Count131072.C048148
import PlattCertificates.Count131072.C048149
import PlattCertificates.Count131072.C048150
import PlattCertificates.Count131072.C048151
import PlattCertificates.Count131072.C048152
import PlattCertificates.Count131072.C048153
import PlattCertificates.Count131072.C048154
import PlattCertificates.Count131072.C048155
import PlattCertificates.Count131072.C048156
import PlattCertificates.Count131072.C048157
import PlattCertificates.Count131072.C048158
import PlattCertificates.Count131072.C048159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000254
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48128 : List PrefixCut := [⟨56,228578808,228578939⟩,
⟨64,260595561,260595710⟩]
theorem checked48128 : checkPrefixCuts (2^48) 6312165377 10 Manual.Count131072.C048128.packed 64 cuts48128 = true := by
 decide +kernel
def pointBounds48128 : List (Nat × Nat × Nat) := [(6312280064,111181858490443,111182245341462)]
theorem point_links_checked48128 : (cuts48128.take 1).map (fun c => (6312165377-1+2*2^10*c.k,111181629911635+c.lower,111182016762523+c.upper)) = pointBounds48128 := by
 decide +kernel
def cuts48129 : List PrefixCut := [⟨64,259296986,259297130⟩]
theorem checked48129 : checkPrefixCuts (2^48) 6312296449 10 Manual.Count131072.C048129.packed 64 cuts48129 = true := by
 decide +kernel
def cuts48130 : List PrefixCut := [⟨25,102870083,102870141⟩,
⟨64,263260131,263260281⟩]
theorem checked48130 : checkPrefixCuts (2^48) 6312427521 10 Manual.Count131072.C048130.packed 64 cuts48130 = true := by
 decide +kernel
def pointBounds48130 : List (Nat × Nat × Nat) := [(6312478720,111182252674265,111182639525504)]
theorem point_links_checked48130 : (cuts48130.take 1).map (fun c => (6312427521-1+2*2^10*c.k,111182149804182+c.lower,111182536655363+c.upper)) = pointBounds48130 := by
 decide +kernel
def cuts48131 : List PrefixCut := [⟨58,231462779,231462907⟩,
⟨64,256477088,256477231⟩]
theorem checked48131 : checkPrefixCuts (2^48) 6312558593 10 Manual.Count131072.C048131.packed 64 cuts48131 = true := by
 decide +kernel
def pointBounds48131 : List (Nat × Nat × Nat) := [(6312677376,111182644527092,111183031378551)]
theorem point_links_checked48131 : (cuts48131.take 1).map (fun c => (6312558593-1+2*2^10*c.k,111182413064313+c.lower,111182799915644+c.upper)) = pointBounds48131 := by
 decide +kernel
def cuts48132 : List PrefixCut := [⟨64,259860501,259860643⟩]
theorem checked48132 : checkPrefixCuts (2^48) 6312689665 10 Manual.Count131072.C048132.packed 64 cuts48132 = true := by
 decide +kernel
def cuts48133 : List PrefixCut := [⟨27,108214150,108214209⟩,
⟨64,257269017,257269160⟩]
theorem checked48133 : checkPrefixCuts (2^48) 6312820737 10 Manual.Count131072.C048133.packed 64 cuts48133 = true := by
 decide +kernel
def pointBounds48133 : List (Nat × Nat × Nat) := [(6312876032,111183037616052,111183424467727)]
theorem point_links_checked48133 : (cuts48133.take 1).map (fun c => (6312820737-1+2*2^10*c.k,111182929401902+c.lower,111183316253518+c.upper)) = pointBounds48133 := by
 decide +kernel
def cuts48134 : List PrefixCut := [⟨60,239919752,239919891⟩,
⟨64,255836953,255837101⟩]
theorem checked48134 : checkPrefixCuts (2^48) 6312951809 10 Manual.Count131072.C048134.packed 64 cuts48134 = true := by
 decide +kernel
def pointBounds48134 : List (Nat × Nat × Nat) := [(6313074688,111183426590671,111183813442569)]
theorem point_links_checked48134 : (cuts48134.take 1).map (fun c => (6312951809-1+2*2^10*c.k,111183186670919+c.lower,111183573522678+c.upper)) = pointBounds48134 := by
 decide +kernel
def cuts48135 : List PrefixCut := [⟨64,261048113,261048263⟩]
theorem checked48135 : checkPrefixCuts (2^48) 6313082881 10 Manual.Count131072.C048135.packed 64 cuts48135 = true := by
 decide +kernel
def cuts48136 : List PrefixCut := [⟨29,116500164,116500229⟩,
⟨64,257386757,257386903⟩]
theorem checked48136 : checkPrefixCuts (2^48) 6313213953 10 Manual.Count131072.C048136.packed 64 cuts48136 = true := by
 decide +kernel
def pointBounds48136 : List (Nat × Nat × Nat) := [(6313273344,111183820056149,111184206908271)]
theorem point_links_checked48136 : (cuts48136.take 1).map (fun c => (6313213953-1+2*2^10*c.k,111183703555985+c.lower,111184090408042+c.upper)) = pointBounds48136 := by
 decide +kernel
def cuts48137 : List PrefixCut := [⟨62,248063517,248063658⟩,
⟨64,257336824,257336969⟩]
theorem checked48137 : checkPrefixCuts (2^48) 6313345025 10 Manual.Count131072.C048137.packed 64 cuts48137 = true := by
 decide +kernel
def pointBounds48137 : List (Nat × Nat × Nat) := [(6313472000,111184209006259,111184595858603)]
theorem point_links_checked48137 : (cuts48137.take 1).map (fun c => (6313345025-1+2*2^10*c.k,111183960942742+c.lower,111184347794945+c.upper)) = pointBounds48137 := by
 decide +kernel
def cuts48138 : List PrefixCut := [⟨64,257197737,257197881⟩]
theorem checked48138 : checkPrefixCuts (2^48) 6313476097 10 Manual.Count131072.C048138.packed 64 cuts48138 = true := by
 decide +kernel
def cuts48139 : List PrefixCut := [⟨31,124829711,124829782⟩,
⟨64,254339195,254339340⟩]
theorem checked48139 : checkPrefixCuts (2^48) 6313607169 10 Manual.Count131072.C048139.packed 64 cuts48139 = true := by
 decide +kernel
def pointBounds48139 : List (Nat × Nat × Nat) := [(6313670656,111184600307014,111184987159577)]
theorem point_links_checked48139 : (cuts48139.take 1).map (fun c => (6313607169-1+2*2^10*c.k,111184475477303+c.lower,111184862329795+c.upper)) = pointBounds48139 := by
 decide +kernel
def cuts48140 : List PrefixCut := [⟨64,257588304,257588447⟩]
theorem checked48140 : checkPrefixCuts (2^48) 6313738241 10 Manual.Count131072.C048140.packed 64 cuts48140 = true := by
 decide +kernel
def pointBounds48140 : List (Nat × Nat × Nat) := [(6313869312,111184987404802,111185374257582)]
theorem point_links_checked48140 : (cuts48140.take 1).map (fun c => (6313738241-1+2*2^10*c.k,111184729816498+c.lower,111185116669135+c.upper)) = pointBounds48140 := by
 decide +kernel
def cuts48141 : List PrefixCut := [⟨64,258875740,258875892⟩]
theorem checked48141 : checkPrefixCuts (2^48) 6313869313 10 Manual.Count131072.C048141.packed 64 cuts48141 = true := by
 decide +kernel
def cuts48142 : List PrefixCut := [⟨33,131820832,131820909⟩,
⟨64,257666745,257666890⟩]
theorem checked48142 : checkPrefixCuts (2^48) 6314000385 10 Manual.Count131072.C048142.packed 64 cuts48142 = true := by
 decide +kernel
def pointBounds48142 : List (Nat × Nat × Nat) := [(6314067968,111185378101374,111185764954383)]
theorem point_links_checked48142 : (cuts48142.take 1).map (fun c => (6314000385-1+2*2^10*c.k,111185246280542+c.lower,111185633133474+c.upper)) = pointBounds48142 := by
 decide +kernel
def cuts48143 : List PrefixCut := [⟨64,259266192,259266341⟩]
theorem checked48143 : checkPrefixCuts (2^48) 6314131457 10 Manual.Count131072.C048143.packed 64 cuts48143 = true := by
 decide +kernel
def cuts48144 : List PrefixCut := [⟨2,7801084,7801088⟩,
⟨64,257254856,257255005⟩]
theorem checked48144 : checkPrefixCuts (2^48) 6314262529 10 Manual.Count131072.C048144.packed 64 cuts48144 = true := by
 decide +kernel
def pointBounds48144 : List (Nat × Nat × Nat) := [(6314266624,111185771014563,111186157867793)]
theorem point_links_checked48144 : (cuts48144.take 1).map (fun c => (6314262529-1+2*2^10*c.k,111185763213479+c.lower,111186150066705+c.upper)) = pointBounds48144 := by
 decide +kernel
def cuts48145 : List PrefixCut := [⟨35,142600082,142600164⟩,
⟨64,262063756,262063903⟩]
theorem checked48145 : checkPrefixCuts (2^48) 6314393601 10 Manual.Count131072.C048145.packed 64 cuts48145 = true := by
 decide +kernel
def pointBounds48145 : List (Nat × Nat × Nat) := [(6314465280,111186163068417,111186549921874)]
theorem point_links_checked48145 : (cuts48145.take 1).map (fun c => (6314393601-1+2*2^10*c.k,111186020468335+c.lower,111186407321710+c.upper)) = pointBounds48145 := by
 decide +kernel
def cuts48146 : List PrefixCut := [⟨64,262370358,262370506⟩]
theorem checked48146 : checkPrefixCuts (2^48) 6314524673 10 Manual.Count131072.C048146.packed 64 cuts48146 = true := by
 decide +kernel
def cuts48147 : List PrefixCut := [⟨4,15868641,15868649⟩,
⟨64,256436503,256436653⟩]
theorem checked48147 : checkPrefixCuts (2^48) 6314655745 10 Manual.Count131072.C048147.packed 64 cuts48147 = true := by
 decide +kernel
def pointBounds48147 : List (Nat × Nat × Nat) := [(6314663936,111186560771090,111186947624768)]
theorem point_links_checked48147 : (cuts48147.take 1).map (fun c => (6314655745-1+2*2^10*c.k,111186544902449+c.lower,111186931756119+c.upper)) = pointBounds48147 := by
 decide +kernel
def cuts48148 : List PrefixCut := [⟨37,149544659,149544747⟩,
⟨64,259105593,259105744⟩]
theorem checked48148 : checkPrefixCuts (2^48) 6314786817 10 Manual.Count131072.C048148.packed 64 cuts48148 = true := by
 decide +kernel
def pointBounds48148 : List (Nat × Nat × Nat) := [(6314862592,111186950883611,111187337737519)]
theorem point_links_checked48148 : (cuts48148.take 1).map (fun c => (6314786817-1+2*2^10*c.k,111186801338952+c.lower,111187188192772+c.upper)) = pointBounds48148 := by
 decide +kernel
def cuts48149 : List PrefixCut := [⟨64,255846433,255846579⟩]
theorem checked48149 : checkPrefixCuts (2^48) 6314917889 10 Manual.Count131072.C048149.packed 64 cuts48149 = true := by
 decide +kernel
def cuts48150 : List PrefixCut := [⟨6,23132889,23132902⟩,
⟨64,258292548,258292691⟩]
theorem checked48150 : checkPrefixCuts (2^48) 6315048961 10 Manual.Count131072.C048150.packed 64 cuts48150 = true := by
 decide +kernel
def pointBounds48150 : List (Nat × Nat × Nat) := [(6315061248,111187339423867,111187726277997)]
theorem point_links_checked48150 : (cuts48150.take 1).map (fun c => (6315048961-1+2*2^10*c.k,111187316290978+c.lower,111187703145095+c.upper)) = pointBounds48150 := by
 decide +kernel
def cuts48151 : List PrefixCut := [⟨39,157558055,157558146⟩,
⟨64,256638088,256638236⟩]
theorem checked48151 : checkPrefixCuts (2^48) 6315180033 10 Manual.Count131072.C048151.packed 64 cuts48151 = true := by
 decide +kernel
def pointBounds48151 : List (Nat × Nat × Nat) := [(6315259904,111187732141581,111188118995932)]
theorem point_links_checked48151 : (cuts48151.take 1).map (fun c => (6315180033-1+2*2^10*c.k,111187574583526+c.lower,111187961437786+c.upper)) = pointBounds48151 := by
 decide +kernel
def cuts48152 : List PrefixCut := [⟨64,259841749,259841894⟩]
theorem checked48152 : checkPrefixCuts (2^48) 6315311105 10 Manual.Count131072.C048152.packed 64 cuts48152 = true := by
 decide +kernel
def cuts48153 : List PrefixCut := [⟨8,32134430,32134449⟩,
⟨64,259791811,259791963⟩]
theorem checked48153 : checkPrefixCuts (2^48) 6315442177 10 Manual.Count131072.C048153.packed 64 cuts48153 = true := by
 decide +kernel
def pointBounds48153 : List (Nat × Nat × Nat) := [(6315458560,111188123197793,111188510052365)]
theorem point_links_checked48153 : (cuts48153.take 1).map (fun c => (6315442177-1+2*2^10*c.k,111188091063363+c.lower,111188477917916+c.upper)) = pointBounds48153 := by
 decide +kernel
def cuts48154 : List PrefixCut := [⟨41,165793265,165793357⟩,
⟨64,258360225,258360370⟩]
theorem checked48154 : checkPrefixCuts (2^48) 6315573249 10 Manual.Count131072.C048154.packed 64 cuts48154 = true := by
 decide +kernel
def pointBounds48154 : List (Nat × Nat × Nat) := [(6315657216,111188516648439,111188903503236)]
theorem point_links_checked48154 : (cuts48154.take 1).map (fun c => (6315573249-1+2*2^10*c.k,111188350855174+c.lower,111188737709879+c.upper)) = pointBounds48154 := by
 decide +kernel
def cuts48155 : List PrefixCut := [⟨64,254611254,254611396⟩]
theorem checked48155 : checkPrefixCuts (2^48) 6315704321 10 Manual.Count131072.C048155.packed 64 cuts48155 = true := by
 decide +kernel
def cuts48156 : List PrefixCut := [⟨10,39842419,39842441⟩,
⟨64,257458206,257458351⟩]
theorem checked48156 : checkPrefixCuts (2^48) 6315835393 10 Manual.Count131072.C048156.packed 64 cuts48156 = true := by
 decide +kernel
def pointBounds48156 : List (Nat × Nat × Nat) := [(6315855872,111188903669072,111189290524086)]
theorem point_links_checked48156 : (cuts48156.take 1).map (fun c => (6315835393-1+2*2^10*c.k,111188863826653+c.lower,111189250681645+c.upper)) = pointBounds48156 := by
 decide +kernel
def cuts48157 : List PrefixCut := [⟨43,177147068,177147167⟩,
⟨64,260795265,260795414⟩]
theorem checked48157 : checkPrefixCuts (2^48) 6315966465 10 Manual.Count131072.C048157.packed 64 cuts48157 = true := by
 decide +kernel
def pointBounds48157 : List (Nat × Nat × Nat) := [(6316054528,111189298431927,111189685287163)]
theorem point_links_checked48157 : (cuts48157.take 1).map (fun c => (6315966465-1+2*2^10*c.k,111189121284859+c.lower,111189508139996+c.upper)) = pointBounds48157 := by
 decide +kernel
def cuts48158 : List PrefixCut := [⟨64,257848604,257848752⟩]
theorem checked48158 : checkPrefixCuts (2^48) 6316097537 10 Manual.Count131072.C048158.packed 64 cuts48158 = true := by
 decide +kernel
def cuts48159 : List PrefixCut := [⟨12,48307023,48307051⟩,
⟨64,256506348,256506499⟩]
theorem checked48159 : checkPrefixCuts (2^48) 6316228609 10 Manual.Count131072.C048159.packed 64 cuts48159 = true := by
 decide +kernel
def pointBounds48159 : List (Nat × Nat × Nat) := [(6316253184,111189688235751,111190075091213)]
theorem point_links_checked48159 : (cuts48159.take 1).map (fun c => (6316228609-1+2*2^10*c.k,111189639928728+c.lower,111190026784162+c.upper)) = pointBounds48159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000254
