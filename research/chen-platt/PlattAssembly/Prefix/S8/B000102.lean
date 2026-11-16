import PlattAssemblyKernel
import PlattCertificates.Count131072.C073264
import PlattCertificates.Count131072.C073265
import PlattCertificates.Count131072.C073266
import PlattCertificates.Count131072.C073267
import PlattCertificates.Count131072.C073268
import PlattCertificates.Count131072.C073269
import PlattCertificates.Count131072.C073270
import PlattCertificates.Count131072.C073271
import PlattCertificates.Count131072.C073272
import PlattCertificates.Count131072.C073273
import PlattCertificates.Count131072.C073274
import PlattCertificates.Count131072.C073275
import PlattCertificates.Count131072.C073276
import PlattCertificates.Count131072.C073277
import PlattCertificates.Count131072.C073278
import PlattCertificates.Count131072.C073279
import PlattCertificates.Count131072.C073280
import PlattCertificates.Count131072.C073281
import PlattCertificates.Count131072.C073282
import PlattCertificates.Count131072.C073283
import PlattCertificates.Count131072.C073284
import PlattCertificates.Count131072.C073285
import PlattCertificates.Count131072.C073286
import PlattCertificates.Count131072.C073287
import PlattCertificates.Count131072.C073288
import PlattCertificates.Count131072.C073289
import PlattCertificates.Count131072.C073290
import PlattCertificates.Count131072.C073291
import PlattCertificates.Count131072.C073292
import PlattCertificates.Count131072.C073293
import PlattCertificates.Count131072.C073294
import PlattCertificates.Count131072.C073295
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73264 : List PrefixCut := [⟨32,82067827,82067876⟩,
⟨64,165717258,165717355⟩]
theorem checked73264 : checkPrefixCuts (2^48) 9606791169 10 Manual.Count131072.C073264.packed 64 cuts73264 = true := by
 decide +kernel
def pointBounds73264 : List (Nat × Nat × Nat) := [(9606856704,116372240260475,116372630096615)]
theorem point_links_checked73264 : (cuts73264.take 1).map (fun c => (9606791169-1+2*2^10*c.k,116372158192648+c.lower,116372548028739+c.upper)) = pointBounds73264 := by
 decide +kernel
def cuts73265 : List PrefixCut := [⟨64,165099722,165099818⟩]
theorem checked73265 : checkPrefixCuts (2^48) 9606922241 10 Manual.Count131072.C073265.packed 64 cuts73265 = true := by
 decide +kernel
def cuts73266 : List PrefixCut := [⟨51,133777483,133777552⟩,
⟨64,167822242,167822331⟩]
theorem checked73266 : checkPrefixCuts (2^48) 9607053313 10 Manual.Count131072.C073266.packed 64 cuts73266 = true := by
 decide +kernel
def pointBounds73266 : List (Nat × Nat × Nat) := [(9607157760,116372622787111,116373012623464)]
theorem point_links_checked73266 : (cuts73266.take 1).map (fun c => (9607053313-1+2*2^10*c.k,116372489009628+c.lower,116372878845912+c.upper)) = pointBounds73266 := by
 decide +kernel
def cuts73267 : List PrefixCut := [⟨64,167116791,167116893⟩]
theorem checked73267 : checkPrefixCuts (2^48) 9607184385 10 Manual.Count131072.C073267.packed 64 cuts73267 = true := by
 decide +kernel
def cuts73268 : List PrefixCut := [⟨64,163950356,163950453⟩]
theorem checked73268 : checkPrefixCuts (2^48) 9607315457 10 Manual.Count131072.C073268.packed 64 cuts73268 = true := by
 decide +kernel
def cuts73269 : List PrefixCut := [⟨6,16142954,16142965⟩,
⟨64,168957966,168958069⟩]
theorem checked73269 : checkPrefixCuts (2^48) 9607446529 10 Manual.Count131072.C073269.packed 64 cuts73269 = true := by
 decide +kernel
def pointBounds73269 : List (Nat × Nat × Nat) := [(9607458816,116373004041971,116373393878554)]
theorem point_links_checked73269 : (cuts73269.take 1).map (fun c => (9607446529-1+2*2^10*c.k,116372987899017+c.lower,116373377735589+c.upper)) = pointBounds73269 := by
 decide +kernel
def cuts73270 : List PrefixCut := [⟨64,168018158,168018262⟩]
theorem checked73270 : checkPrefixCuts (2^48) 9607577601 10 Manual.Count131072.C073270.packed 64 cuts73270 = true := by
 decide +kernel
def cuts73271 : List PrefixCut := [⟨25,63954692,63954732⟩,
⟨64,166873289,166873396⟩]
theorem checked73271 : checkPrefixCuts (2^48) 9607708673 10 Manual.Count131072.C073271.packed 64 cuts73271 = true := by
 decide +kernel
def pointBounds73271 : List (Nat × Nat × Nat) := [(9607759872,116373388829833,116373778666652)]
theorem point_links_checked73271 : (cuts73271.take 1).map (fun c => (9607708673-1+2*2^10*c.k,116373324875141+c.lower,116373714711920+c.upper)) = pointBounds73271 := by
 decide +kernel
def cuts73272 : List PrefixCut := [⟨64,167749907,167750005⟩]
theorem checked73272 : checkPrefixCuts (2^48) 9607839745 10 Manual.Count131072.C073272.packed 64 cuts73272 = true := by
 decide +kernel
def cuts73273 : List PrefixCut := [⟨44,116011529,116011601⟩,
⟨64,168831568,168831672⟩]
theorem checked73273 : checkPrefixCuts (2^48) 9607970817 10 Manual.Count131072.C073273.packed 64 cuts73273 = true := by
 decide +kernel
def pointBounds73273 : List (Nat × Nat × Nat) := [(9608060928,116373775509866,116374165346922)]
theorem point_links_checked73273 : (cuts73273.take 1).map (fun c => (9607970817-1+2*2^10*c.k,116373659498337+c.lower,116374049335321+c.upper)) = pointBounds73273 := by
 decide +kernel
def cuts73274 : List PrefixCut := [⟨64,165430994,165431095⟩]
theorem checked73274 : checkPrefixCuts (2^48) 9608101889 10 Manual.Count131072.C073274.packed 64 cuts73274 = true := by
 decide +kernel
def cuts73275 : List PrefixCut := [⟨63,165077222,165077318⟩,
⟨64,167772342,167772439⟩]
theorem checked73275 : checkPrefixCuts (2^48) 9608232961 10 Manual.Count131072.C073275.packed 64 cuts73275 = true := by
 decide +kernel
def pointBounds73275 : List (Nat × Nat × Nat) := [(9608361984,116374158838121,116374548675406)]
theorem point_links_checked73275 : (cuts73275.take 1).map (fun c => (9608232961-1+2*2^10*c.k,116373993760899+c.lower,116374383598088+c.upper)) = pointBounds73275 := by
 decide +kernel
def cuts73276 : List PrefixCut := [⟨64,168209476,168209568⟩]
theorem checked73276 : checkPrefixCuts (2^48) 9608364033 10 Manual.Count131072.C073276.packed 64 cuts73276 = true := by
 decide +kernel
def cuts73277 : List PrefixCut := [⟨64,166566702,166566807⟩]
theorem checked73277 : checkPrefixCuts (2^48) 9608495105 10 Manual.Count131072.C073277.packed 64 cuts73277 = true := by
 decide +kernel
def cuts73278 : List PrefixCut := [⟨18,46958157,46958187⟩,
⟨64,168263464,168263568⟩]
theorem checked73278 : checkPrefixCuts (2^48) 9608626177 10 Manual.Count131072.C073278.packed 64 cuts73278 = true := by
 decide +kernel
def pointBounds73278 : List (Nat × Nat × Nat) := [(9608663040,116374543267576,116374933105089)]
theorem point_links_checked73278 : (cuts73278.take 1).map (fun c => (9608626177-1+2*2^10*c.k,116374496309419+c.lower,116374886146902+c.upper)) = pointBounds73278 := by
 decide +kernel
def cuts73279 : List PrefixCut := [⟨64,166298513,166298619⟩]
theorem checked73279 : checkPrefixCuts (2^48) 9608757249 10 Manual.Count131072.C073279.packed 64 cuts73279 = true := by
 decide +kernel
def cuts73280 : List PrefixCut := [⟨37,96403476,96403532⟩,
⟨64,166384129,166384227⟩]
theorem checked73280 : checkPrefixCuts (2^48) 9608888321 10 Manual.Count131072.C073280.packed 64 cuts73280 = true := by
 decide +kernel
def pointBounds73280 : List (Nat × Nat × Nat) := [(9608964096,116374927274872,116375317112621)]
theorem point_links_checked73280 : (cuts73280.take 1).map (fun c => (9608888321-1+2*2^10*c.k,116374830871396+c.lower,116375220709089+c.upper)) = pointBounds73280 := by
 decide +kernel
def cuts73281 : List PrefixCut := [⟨64,167612148,167612251⟩]
theorem checked73281 : checkPrefixCuts (2^48) 9609019393 10 Manual.Count131072.C073281.packed 64 cuts73281 = true := by
 decide +kernel
def cuts73282 : List PrefixCut := [⟨56,146255982,146256067⟩,
⟨64,166789678,166789776⟩]
theorem checked73282 : checkPrefixCuts (2^48) 9609150465 10 Manual.Count131072.C073282.packed 64 cuts73282 = true := by
 decide +kernel
def pointBounds73282 : List (Nat × Nat × Nat) := [(9609265152,116375311123655,116375700961634)]
theorem point_links_checked73282 : (cuts73282.take 1).map (fun c => (9609150465-1+2*2^10*c.k,116375164867673+c.lower,116375554705567+c.upper)) = pointBounds73282 := by
 decide +kernel
def cuts73283 : List PrefixCut := [⟨64,165586440,165586539⟩]
theorem checked73283 : checkPrefixCuts (2^48) 9609281537 10 Manual.Count131072.C073283.packed 64 cuts73283 = true := by
 decide +kernel
def cuts73284 : List PrefixCut := [⟨64,167078040,167078144⟩]
theorem checked73284 : checkPrefixCuts (2^48) 9609412609 10 Manual.Count131072.C073284.packed 64 cuts73284 = true := by
 decide +kernel
def cuts73285 : List PrefixCut := [⟨11,29261856,29261873⟩,
⟨64,167544421,167544517⟩]
theorem checked73285 : checkPrefixCuts (2^48) 9609543681 10 Manual.Count131072.C073285.packed 64 cuts73285 = true := by
 decide +kernel
def pointBounds73285 : List (Nat × Nat × Nat) := [(9609566208,116375693583687,116376083421899)]
theorem point_links_checked73285 : (cuts73285.take 1).map (fun c => (9609543681-1+2*2^10*c.k,116375664321831+c.lower,116376054160026+c.upper)) = pointBounds73285 := by
 decide +kernel
def cuts73286 : List PrefixCut := [⟨64,167073490,167073584⟩]
theorem checked73286 : checkPrefixCuts (2^48) 9609674753 10 Manual.Count131072.C073286.packed 64 cuts73286 = true := by
 decide +kernel
def cuts73287 : List PrefixCut := [⟨30,78351523,78351574⟩,
⟨64,168916478,168916585⟩]
theorem checked73287 : checkPrefixCuts (2^48) 9609805825 10 Manual.Count131072.C073287.packed 64 cuts73287 = true := by
 decide +kernel
def pointBounds73287 : List (Nat × Nat × Nat) := [(9609867264,116376077291265,116376467129701)]
theorem point_links_checked73287 : (cuts73287.take 1).map (fun c => (9609805825-1+2*2^10*c.k,116375998939742+c.lower,116376388778127+c.upper)) = pointBounds73287 := by
 decide +kernel
def cuts73288 : List PrefixCut := [⟨64,167566853,167566948⟩]
theorem checked73288 : checkPrefixCuts (2^48) 9609936897 10 Manual.Count131072.C073288.packed 64 cuts73288 = true := by
 decide +kernel
def cuts73289 : List PrefixCut := [⟨49,128522019,128522097⟩,
⟨64,166510151,166510253⟩]
theorem checked73289 : checkPrefixCuts (2^48) 9610067969 10 Manual.Count131072.C073289.packed 64 cuts73289 = true := by
 decide +kernel
def pointBounds73289 : List (Nat × Nat × Nat) := [(9610168320,116376463945092,116376853783757)]
theorem point_links_checked73289 : (cuts73289.take 1).map (fun c => (9610067969-1+2*2^10*c.k,116376335423073+c.lower,116376725261660+c.upper)) = pointBounds73289 := by
 decide +kernel
def cuts73290 : List PrefixCut := [⟨64,167913741,167913843⟩]
theorem checked73290 : checkPrefixCuts (2^48) 9610199041 10 Manual.Count131072.C073290.packed 64 cuts73290 = true := by
 decide +kernel
def cuts73291 : List PrefixCut := [⟨64,166124867,166124960⟩]
theorem checked73291 : checkPrefixCuts (2^48) 9610330113 10 Manual.Count131072.C073291.packed 64 cuts73291 = true := by
 decide +kernel
def cuts73292 : List PrefixCut := [⟨4,10338796,10338801⟩,
⟨64,170105778,170105880⟩]
theorem checked73292 : checkPrefixCuts (2^48) 9610461185 10 Manual.Count131072.C073292.packed 64 cuts73292 = true := by
 decide +kernel
def pointBounds73292 : List (Nat × Nat × Nat) := [(9610469376,116376846310628,116377236149517)]
theorem point_links_checked73292 : (cuts73292.take 1).map (fun c => (9610461185-1+2*2^10*c.k,116376835971832+c.lower,116377225810716+c.upper)) = pointBounds73292 := by
 decide +kernel
def cuts73293 : List PrefixCut := [⟨64,167467571,167467667⟩]
theorem checked73293 : checkPrefixCuts (2^48) 9610592257 10 Manual.Count131072.C073293.packed 64 cuts73293 = true := by
 decide +kernel
def cuts73294 : List PrefixCut := [⟨23,61591646,61591679⟩,
⟨64,167904603,167904698⟩]
theorem checked73294 : checkPrefixCuts (2^48) 9610723329 10 Manual.Count131072.C073294.packed 64 cuts73294 = true := by
 decide +kernel
def pointBounds73294 : List (Nat × Nat × Nat) := [(9610770432,116377235136827,116377624975942)]
theorem point_links_checked73294 : (cuts73294.take 1).map (fun c => (9610723329-1+2*2^10*c.k,116377173545181+c.lower,116377563384263+c.upper)) = pointBounds73294 := by
 decide +kernel
def cuts73295 : List PrefixCut := [⟨64,166701526,166701623⟩]
theorem checked73295 : checkPrefixCuts (2^48) 9610854401 10 Manual.Count131072.C073295.packed 64 cuts73295 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000102
