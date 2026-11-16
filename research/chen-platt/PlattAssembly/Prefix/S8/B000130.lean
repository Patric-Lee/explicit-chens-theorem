import PlattAssemblyKernel
import PlattCertificates.Count131072.C074160
import PlattCertificates.Count131072.C074161
import PlattCertificates.Count131072.C074162
import PlattCertificates.Count131072.C074163
import PlattCertificates.Count131072.C074164
import PlattCertificates.Count131072.C074165
import PlattCertificates.Count131072.C074166
import PlattCertificates.Count131072.C074167
import PlattCertificates.Count131072.C074168
import PlattCertificates.Count131072.C074169
import PlattCertificates.Count131072.C074170
import PlattCertificates.Count131072.C074171
import PlattCertificates.Count131072.C074172
import PlattCertificates.Count131072.C074173
import PlattCertificates.Count131072.C074174
import PlattCertificates.Count131072.C074175
import PlattCertificates.Count131072.C074176
import PlattCertificates.Count131072.C074177
import PlattCertificates.Count131072.C074178
import PlattCertificates.Count131072.C074179
import PlattCertificates.Count131072.C074180
import PlattCertificates.Count131072.C074181
import PlattCertificates.Count131072.C074182
import PlattCertificates.Count131072.C074183
import PlattCertificates.Count131072.C074184
import PlattCertificates.Count131072.C074185
import PlattCertificates.Count131072.C074186
import PlattCertificates.Count131072.C074187
import PlattCertificates.Count131072.C074188
import PlattCertificates.Count131072.C074189
import PlattCertificates.Count131072.C074190
import PlattCertificates.Count131072.C074191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74160 : List PrefixCut := [⟨64,164497426,164497524⟩]
theorem checked74160 : checkPrefixCuts (2^48) 9724231681 10 Manual.Count131072.C074160.packed 64 cuts74160 = true := by
 decide +kernel
def cuts74161 : List PrefixCut := [⟨40,101916080,101916138⟩,
⟨64,163308451,163308548⟩]
theorem checked74161 : checkPrefixCuts (2^48) 9724362753 10 Manual.Count131072.C074161.packed 64 cuts74161 = true := by
 decide +kernel
def pointBounds74161 : List (Nat × Nat × Nat) := [(9724444672,116521227866864,116521617791853)]
theorem point_links_checked74161 : (cuts74161.take 1).map (fun c => (9724362753-1+2*2^10*c.k,116521125950784+c.lower,116521515875715+c.upper)) = pointBounds74161 := by
 decide +kernel
def cuts74162 : List PrefixCut := [⟨64,164782436,164782535⟩]
theorem checked74162 : checkPrefixCuts (2^48) 9724493825 10 Manual.Count131072.C074162.packed 64 cuts74162 = true := by
 decide +kernel
def cuts74163 : List PrefixCut := [⟨61,156849512,156849603⟩,
⟨64,164635494,164635589⟩]
theorem checked74163 : checkPrefixCuts (2^48) 9724624897 10 Manual.Count131072.C074163.packed 64 cuts74163 = true := by
 decide +kernel
def pointBounds74163 : List (Nat × Nat × Nat) := [(9724749824,116521610891183,116522000816401)]
theorem point_links_checked74163 : (cuts74163.take 1).map (fun c => (9724624897-1+2*2^10*c.k,116521454041671+c.lower,116521843966798+c.upper)) = pointBounds74163 := by
 decide +kernel
def cuts74164 : List PrefixCut := [⟨64,168830146,168830245⟩]
theorem checked74164 : checkPrefixCuts (2^48) 9724755969 10 Manual.Count131072.C074164.packed 64 cuts74164 = true := by
 decide +kernel
def cuts74165 : List PrefixCut := [⟨64,163733806,163733909⟩]
theorem checked74165 : checkPrefixCuts (2^48) 9724887041 10 Manual.Count131072.C074165.packed 64 cuts74165 = true := by
 decide +kernel
def cuts74166 : List PrefixCut := [⟨18,47814373,47814399⟩,
⟨64,164397291,164397385⟩]
theorem checked74166 : checkPrefixCuts (2^48) 9725018113 10 Manual.Count131072.C074166.packed 64 cuts74166 = true := by
 decide +kernel
def pointBounds74166 : List (Nat × Nat × Nat) := [(9725054976,116521999055490,116522388980940)]
theorem point_links_checked74166 : (cuts74166.take 1).map (fun c => (9725018113-1+2*2^10*c.k,116521951241117+c.lower,116522341166541+c.upper)) = pointBounds74166 := by
 decide +kernel
def cuts74167 : List PrefixCut := [⟨64,164337191,164337291⟩]
theorem checked74167 : checkPrefixCuts (2^48) 9725149185 10 Manual.Count131072.C074167.packed 64 cuts74167 = true := by
 decide +kernel
def cuts74168 : List PrefixCut := [⟨39,99359538,99359596⟩,
⟨64,164537566,164537662⟩]
theorem checked74168 : checkPrefixCuts (2^48) 9725280257 10 Manual.Count131072.C074168.packed 64 cuts74168 = true := by
 decide +kernel
def pointBounds74168 : List (Nat × Nat × Nat) := [(9725360128,116522379335137,116522769260813)]
theorem point_links_checked74168 : (cuts74168.take 1).map (fun c => (9725280257-1+2*2^10*c.k,116522279975599+c.lower,116522669901217+c.upper)) = pointBounds74168 := by
 decide +kernel
def cuts74169 : List PrefixCut := [⟨64,166185044,166185138⟩]
theorem checked74169 : checkPrefixCuts (2^48) 9725411329 10 Manual.Count131072.C074169.packed 64 cuts74169 = true := by
 decide +kernel
def cuts74170 : List PrefixCut := [⟨60,152667131,152667225⟩,
⟨64,163375465,163375565⟩]
theorem checked74170 : checkPrefixCuts (2^48) 9725542401 10 Manual.Count131072.C074170.packed 64 cuts74170 = true := by
 decide +kernel
def pointBounds74170 : List (Nat × Nat × Nat) := [(9725665280,116522763365340,116523153291242)]
theorem point_links_checked74170 : (cuts74170.take 1).map (fun c => (9725542401-1+2*2^10*c.k,116522610698209+c.lower,116523000624017+c.upper)) = pointBounds74170 := by
 decide +kernel
def cuts74171 : List PrefixCut := [⟨64,164357268,164357364⟩]
theorem checked74171 : checkPrefixCuts (2^48) 9725673473 10 Manual.Count131072.C074171.packed 64 cuts74171 = true := by
 decide +kernel
def cuts74172 : List PrefixCut := [⟨64,165223278,165223375⟩]
theorem checked74172 : checkPrefixCuts (2^48) 9725804545 10 Manual.Count131072.C074172.packed 64 cuts74172 = true := by
 decide +kernel
def cuts74173 : List PrefixCut := [⟨17,44394877,44394903⟩,
⟨64,165163179,165163273⟩]
theorem checked74173 : checkPrefixCuts (2^48) 9725935617 10 Manual.Count131072.C074173.packed 64 cuts74173 = true := by
 decide +kernel
def pointBounds74173 : List (Nat × Nat × Nat) := [(9725970432,116523148049097,116523537975224)]
theorem point_links_checked74173 : (cuts74173.take 1).map (fun c => (9725935617-1+2*2^10*c.k,116523103654220+c.lower,116523493580321+c.upper)) = pointBounds74173 := by
 decide +kernel
def cuts74174 : List PrefixCut := [⟨64,167331447,167331545⟩]
theorem checked74174 : checkPrefixCuts (2^48) 9726066689 10 Manual.Count131072.C074174.packed 64 cuts74174 = true := by
 decide +kernel
def cuts74175 : List PrefixCut := [⟨38,100334127,100334181⟩,
⟨64,167618603,167618694⟩]
theorem checked74175 : checkPrefixCuts (2^48) 9726197761 10 Manual.Count131072.C074175.packed 64 cuts74175 = true := by
 decide +kernel
def pointBounds74175 : List (Nat × Nat × Nat) := [(9726275584,116523536482973,116523926409320)]
theorem point_links_checked74175 : (cuts74175.take 1).map (fun c => (9726197761-1+2*2^10*c.k,116523436148846+c.lower,116523826075139+c.upper)) = pointBounds74175 := by
 decide +kernel
def cuts74176 : List PrefixCut := [⟨64,166834974,166835076⟩]
theorem checked74176 : checkPrefixCuts (2^48) 9726328833 10 Manual.Count131072.C074176.packed 64 cuts74176 = true := by
 decide +kernel
def cuts74177 : List PrefixCut := [⟨59,151061109,151061204⟩,
⟨64,163504756,163504858⟩]
theorem checked74177 : checkPrefixCuts (2^48) 9726459905 10 Manual.Count131072.C074177.packed 64 cuts74177 = true := by
 decide +kernel
def pointBounds74177 : List (Nat × Nat × Nat) := [(9726580736,116523921663532,116524311590113)]
theorem point_links_checked74177 : (cuts74177.take 1).map (fun c => (9726459905-1+2*2^10*c.k,116523770602423+c.lower,116524160528909+c.upper)) = pointBounds74177 := by
 decide +kernel
def cuts74178 : List PrefixCut := [⟨64,164775835,164775937⟩]
theorem checked74178 : checkPrefixCuts (2^48) 9726590977 10 Manual.Count131072.C074178.packed 64 cuts74178 = true := by
 decide +kernel
def cuts74179 : List PrefixCut := [⟨64,164600001,164600102⟩]
theorem checked74179 : checkPrefixCuts (2^48) 9726722049 10 Manual.Count131072.C074179.packed 64 cuts74179 = true := by
 decide +kernel
def cuts74180 : List PrefixCut := [⟨16,41294342,41294366⟩,
⟨64,163150893,163150991⟩]
theorem checked74180 : checkPrefixCuts (2^48) 9726853121 10 Manual.Count131072.C074180.packed 64 cuts74180 = true := by
 decide +kernel
def pointBounds74180 : List (Nat × Nat × Nat) := [(9726885888,116524304777357,116524694704172)]
theorem point_links_checked74180 : (cuts74180.take 1).map (fun c => (9726853121-1+2*2^10*c.k,116524263483015+c.lower,116524653409806+c.upper)) = pointBounds74180 := by
 decide +kernel
def cuts74181 : List PrefixCut := [⟨64,164537680,164537784⟩]
theorem checked74181 : checkPrefixCuts (2^48) 9726984193 10 Manual.Count131072.C074181.packed 64 cuts74181 = true := by
 decide +kernel
def cuts74182 : List PrefixCut := [⟨37,95694747,95694808⟩,
⟨64,166329553,166329659⟩]
theorem checked74182 : checkPrefixCuts (2^48) 9727115265 10 Manual.Count131072.C074182.packed 64 cuts74182 = true := by
 decide +kernel
def pointBounds74182 : List (Nat × Nat × Nat) := [(9727191040,116524686866335,116525076793389)]
theorem point_links_checked74182 : (cuts74182.take 1).map (fun c => (9727115265-1+2*2^10*c.k,116524591171588+c.lower,116524981098581+c.upper)) = pointBounds74182 := by
 decide +kernel
def cuts74183 : List PrefixCut := [⟨64,165719649,165719747⟩]
theorem checked74183 : checkPrefixCuts (2^48) 9727246337 10 Manual.Count131072.C074183.packed 64 cuts74183 = true := by
 decide +kernel
def cuts74184 : List PrefixCut := [⟨58,148587321,148587406⟩,
⟨64,163981267,163981361⟩]
theorem checked74184 : checkPrefixCuts (2^48) 9727377409 10 Manual.Count131072.C074184.packed 64 cuts74184 = true := by
 decide +kernel
def pointBounds74184 : List (Nat × Nat × Nat) := [(9727496192,116525071808111,116525461735393)]
theorem point_links_checked74184 : (cuts74184.take 1).map (fun c => (9727377409-1+2*2^10*c.k,116524923220790+c.lower,116525313147987+c.upper)) = pointBounds74184 := by
 decide +kernel
def cuts74185 : List PrefixCut := [⟨64,166004541,166004634⟩]
theorem checked74185 : checkPrefixCuts (2^48) 9727508481 10 Manual.Count131072.C074185.packed 64 cuts74185 = true := by
 decide +kernel
def cuts74186 : List PrefixCut := [⟨64,163947887,163947990⟩]
theorem checked74186 : checkPrefixCuts (2^48) 9727639553 10 Manual.Count131072.C074186.packed 64 cuts74186 = true := by
 decide +kernel
def cuts74187 : List PrefixCut := [⟨15,38049714,38049738⟩,
⟨64,165016277,165016377⟩]
theorem checked74187 : checkPrefixCuts (2^48) 9727770625 10 Manual.Count131072.C074187.packed 64 cuts74187 = true := by
 decide +kernel
def pointBounds74187 : List (Nat × Nat × Nat) := [(9727801344,116525455204199,116525845131710)]
theorem point_links_checked74187 : (cuts74187.take 1).map (fun c => (9727770625-1+2*2^10*c.k,116525417154485+c.lower,116525807081972+c.upper)) = pointBounds74187 := by
 decide +kernel
def cuts74188 : List PrefixCut := [⟨64,166981616,166981710⟩]
theorem checked74188 : checkPrefixCuts (2^48) 9727901697 10 Manual.Count131072.C074188.packed 64 cuts74188 = true := by
 decide +kernel
def cuts74189 : List PrefixCut := [⟨36,90593297,90593350⟩,
⟨64,162581352,162581448⟩]
theorem checked74189 : checkPrefixCuts (2^48) 9728032769 10 Manual.Count131072.C074189.packed 64 cuts74189 = true := by
 decide +kernel
def pointBounds74189 : List (Nat × Nat × Nat) := [(9728106496,116525839745675,116526229673409)]
theorem point_links_checked74189 : (cuts74189.take 1).map (fun c => (9728032769-1+2*2^10*c.k,116525749152378+c.lower,116526139080059+c.upper)) = pointBounds74189 := by
 decide +kernel
def cuts74190 : List PrefixCut := [⟨64,166687763,166687856⟩]
theorem checked74190 : checkPrefixCuts (2^48) 9728163841 10 Manual.Count131072.C074190.packed 64 cuts74190 = true := by
 decide +kernel
def cuts74191 : List PrefixCut := [⟨57,147792108,147792192⟩,
⟨64,165412465,165412559⟩]
theorem checked74191 : checkPrefixCuts (2^48) 9728294913 10 Manual.Count131072.C074191.packed 64 cuts74191 = true := by
 decide +kernel
def pointBounds74191 : List (Nat × Nat × Nat) := [(9728411648,116526226213601,116526616141555)]
theorem point_links_checked74191 : (cuts74191.take 1).map (fun c => (9728294913-1+2*2^10*c.k,116526078421493+c.lower,116526468349363+c.upper)) = pointBounds74191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000130
