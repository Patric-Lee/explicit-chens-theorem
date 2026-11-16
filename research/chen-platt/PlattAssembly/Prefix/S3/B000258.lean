import PlattAssemblyKernel
import PlattCertificates.Count131072.C028256
import PlattCertificates.Count131072.C028257
import PlattCertificates.Count131072.C028258
import PlattCertificates.Count131072.C028259
import PlattCertificates.Count131072.C028260
import PlattCertificates.Count131072.C028261
import PlattCertificates.Count131072.C028262
import PlattCertificates.Count131072.C028263
import PlattCertificates.Count131072.C028264
import PlattCertificates.Count131072.C028265
import PlattCertificates.Count131072.C028266
import PlattCertificates.Count131072.C028267
import PlattCertificates.Count131072.C028268
import PlattCertificates.Count131072.C028269
import PlattCertificates.Count131072.C028270
import PlattCertificates.Count131072.C028271
import PlattCertificates.Count131072.C028272
import PlattCertificates.Count131072.C028273
import PlattCertificates.Count131072.C028274
import PlattCertificates.Count131072.C028275
import PlattCertificates.Count131072.C028276
import PlattCertificates.Count131072.C028277
import PlattCertificates.Count131072.C028278
import PlattCertificates.Count131072.C028279
import PlattCertificates.Count131072.C028280
import PlattCertificates.Count131072.C028281
import PlattCertificates.Count131072.C028282
import PlattCertificates.Count131072.C028283
import PlattCertificates.Count131072.C028284
import PlattCertificates.Count131072.C028285
import PlattCertificates.Count131072.C028286
import PlattCertificates.Count131072.C028287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000258
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28256 : List PrefixCut := [⟨55,195493419,195493529⟩,
⟨128,448757319,448757574⟩]
theorem checked28256 : checkPrefixCuts (2^48) 3707502593 9 Manual.Count131072.C028256.packed 128 cuts28256 = true := by
 decide +kernel
def pointBounds28256 : List (Nat × Nat × Nat) := [(3707558912,104464905541038,104465288434698)]
theorem point_links_checked28256 : (cuts28256.take 1).map (fun c => (3707502593-1+2*2^9*c.k,104464710047619+c.lower,104465092941169+c.upper)) = pointBounds28256 := by
 decide +kernel
def cuts28257 : List PrefixCut := [⟨41,146748023,146748102⟩,
⟨128,452461327,452461576⟩]
theorem checked28257 : checkPrefixCuts (2^48) 3707633665 9 Manual.Count131072.C028257.packed 128 cuts28257 = true := by
 decide +kernel
def pointBounds28257 : List (Nat × Nat × Nat) := [(3707675648,104465305552961,104465688446845)]
theorem point_links_checked28257 : (cuts28257.take 1).map (fun c => (3707633665-1+2*2^9*c.k,104465158804938+c.lower,104465541698743+c.upper)) = pointBounds28257 := by
 decide +kernel
def cuts28258 : List PrefixCut := [⟨27,97322646,97322700⟩,
⟨128,449940210,449940465⟩]
theorem checked28258 : checkPrefixCuts (2^48) 3707764737 9 Manual.Count131072.C028258.packed 128 cuts28258 = true := by
 decide +kernel
def pointBounds28258 : List (Nat × Nat × Nat) := [(3707792384,104465708588911,104466091483019)]
theorem point_links_checked28258 : (cuts28258.take 1).map (fun c => (3707764737-1+2*2^9*c.k,104465611266265+c.lower,104465994160319+c.upper)) = pointBounds28258 := by
 decide +kernel
def cuts28259 : List PrefixCut := [⟨13,45243648,45243671⟩,
⟨127,443396031,443396277⟩,
⟨128,446887874,446888122⟩]
theorem checked28259 : checkPrefixCuts (2^48) 3707895809 9 Manual.Count131072.C028259.packed 128 cuts28259 = true := by
 decide +kernel
def pointBounds28259 : List (Nat × Nat × Nat) := [(3707909120,104466106450123,104466489344455),(3708025856,104466504602506,104466887497061)]
theorem point_links_checked28259 : (cuts28259.take 2).map (fun c => (3707895809-1+2*2^9*c.k,104466061206475+c.lower,104466444100784+c.upper)) = pointBounds28259 := by
 decide +kernel
def cuts28260 : List PrefixCut := [⟨113,399657893,399658115⟩,
⟨128,453779647,453779899⟩]
theorem checked28260 : checkPrefixCuts (2^48) 3708026881 9 Manual.Count131072.C028260.packed 128 cuts28260 = true := by
 decide +kernel
def pointBounds28260 : List (Nat × Nat × Nat) := [(3708142592,104466907752242,104467290647021)]
theorem point_links_checked28260 : (cuts28260.take 1).map (fun c => (3708026881-1+2*2^9*c.k,104466508094349+c.lower,104466890988906+c.upper)) = pointBounds28260 := by
 decide +kernel
def cuts28261 : List PrefixCut := [⟨99,345068220,345068412⟩,
⟨128,448374323,448374573⟩]
theorem checked28261 : checkPrefixCuts (2^48) 3708157953 9 Manual.Count131072.C028261.packed 128 cuts28261 = true := by
 decide +kernel
def pointBounds28261 : List (Nat × Nat × Nat) := [(3708259328,104467306942216,104467689837217)]
theorem point_links_checked28261 : (cuts28261.take 1).map (fun c => (3708157953-1+2*2^9*c.k,104466961873996+c.lower,104467344768805+c.upper)) = pointBounds28261 := by
 decide +kernel
def cuts28262 : List PrefixCut := [⟨85,293897774,293897940⟩,
⟨128,447295745,447295996⟩]
theorem checked28262 : checkPrefixCuts (2^48) 3708289025 9 Manual.Count131072.C028262.packed 128 cuts28262 = true := by
 decide +kernel
def pointBounds28262 : List (Nat × Nat × Nat) := [(3708376064,104467704146093,104468087041318)]
theorem point_links_checked28262 : (cuts28262.take 1).map (fun c => (3708289025-1+2*2^9*c.k,104467410248319+c.lower,104467793143378+c.upper)) = pointBounds28262 := by
 decide +kernel
def cuts28263 : List PrefixCut := [⟨71,252977434,252977577⟩,
⟨128,454870068,454870325⟩]
theorem checked28263 : checkPrefixCuts (2^48) 3708420097 9 Manual.Count131072.C028263.packed 128 cuts28263 = true := by
 decide +kernel
def pointBounds28263 : List (Nat × Nat × Nat) := [(3708492800,104468110521498,104468493416951)]
theorem point_links_checked28263 : (cuts28263.take 1).map (fun c => (3708420097-1+2*2^9*c.k,104467857544064+c.lower,104468240439374+c.upper)) = pointBounds28263 := by
 decide +kernel
def cuts28264 : List PrefixCut := [⟨57,200599173,200599285⟩,
⟨128,446581149,446581397⟩]
theorem checked28264 : checkPrefixCuts (2^48) 3708551169 9 Manual.Count131072.C028264.packed 128 cuts28264 = true := by
 decide +kernel
def pointBounds28264 : List (Nat × Nat × Nat) := [(3708609536,104468513013305,104468895908984)]
theorem point_links_checked28264 : (cuts28264.take 1).map (fun c => (3708551169-1+2*2^9*c.k,104468312414132+c.lower,104468695309699+c.upper)) = pointBounds28264 := by
 decide +kernel
def cuts28265 : List PrefixCut := [⟨43,150956643,150956726⟩,
⟨128,448083249,448083495⟩]
theorem checked28265 : checkPrefixCuts (2^48) 3708682241 9 Manual.Count131072.C028265.packed 128 cuts28265 = true := by
 decide +kernel
def pointBounds28265 : List (Nat × Nat × Nat) := [(3708726272,104468909951924,104469292847822)]
theorem point_links_checked28265 : (cuts28265.take 1).map (fun c => (3708682241-1+2*2^9*c.k,104468758995281+c.lower,104469141891096+c.upper)) = pointBounds28265 := by
 decide +kernel
def cuts28266 : List PrefixCut := [⟨29,100179046,100179101⟩,
⟨128,453000386,453000639⟩]
theorem checked28266 : checkPrefixCuts (2^48) 3708813313 9 Manual.Count131072.C028266.packed 128 cuts28266 = true := by
 decide +kernel
def pointBounds28266 : List (Nat × Nat × Nat) := [(3708843008,104469307257576,104469690153692)]
theorem point_links_checked28266 : (cuts28266.take 1).map (fun c => (3708813313-1+2*2^9*c.k,104469207078530+c.lower,104469589974591+c.upper)) = pointBounds28266 := by
 decide +kernel
def cuts28267 : List PrefixCut := [⟨15,54034165,54034195⟩,
⟨128,451997870,451998118⟩]
theorem checked28267 : checkPrefixCuts (2^48) 3708944385 9 Manual.Count131072.C028267.packed 128 cuts28267 = true := by
 decide +kernel
def pointBounds28267 : List (Nat × Nat × Nat) := [(3708959744,104469714113081,104470097009425)]
theorem point_links_checked28267 : (cuts28267.take 1).map (fun c => (3708944385-1+2*2^9*c.k,104469660078916+c.lower,104470042975230+c.upper)) = pointBounds28267 := by
 decide +kernel
def cuts28268 : List PrefixCut := [⟨1,3718519,3718521⟩,
⟨115,404856844,404857069⟩,
⟨128,450615869,450616119⟩]
theorem checked28268 : checkPrefixCuts (2^48) 3709075457 9 Manual.Count131072.C028268.packed 128 cuts28268 = true := by
 decide +kernel
def pointBounds28268 : List (Nat × Nat × Nat) := [(3709076480,104470115795305,104470498691869),(3709193216,104470516933630,104470899830417)]
theorem point_links_checked28268 : (cuts28268.take 2).map (fun c => (3709075457-1+2*2^9*c.k,104470112076786+c.lower,104470494973348+c.upper)) = pointBounds28268 := by
 decide +kernel
def cuts28269 : List PrefixCut := [⟨101,358022611,358022810⟩,
⟨128,455608249,455608504⟩]
theorem checked28269 : checkPrefixCuts (2^48) 3709206529 9 Manual.Count131072.C028269.packed 128 cuts28269 = true := by
 decide +kernel
def pointBounds28269 : List (Nat × Nat × Nat) := [(3709309952,104470920715266,104471303612277)]
theorem point_links_checked28269 : (cuts28269.take 1).map (fun c => (3709206529-1+2*2^9*c.k,104470562692655+c.lower,104470945589467+c.upper)) = pointBounds28269 := by
 decide +kernel
def cuts28270 : List PrefixCut := [⟨87,309142783,309142956⟩,
⟨128,454529896,454530151⟩]
theorem checked28270 : checkPrefixCuts (2^48) 3709337601 9 Manual.Count131072.C028270.packed 128 cuts28270 = true := by
 decide +kernel
def pointBounds28270 : List (Nat × Nat × Nat) := [(3709426688,104471327443687,104471710340927)]
theorem point_links_checked28270 : (cuts28270.take 1).map (fun c => (3709337601-1+2*2^9*c.k,104471018300904+c.lower,104471401197971+c.upper)) = pointBounds28270 := by
 decide +kernel
def cuts28271 : List PrefixCut := [⟨73,251767672,251767820⟩,
⟨128,449278132,449278390⟩]
theorem checked28271 : checkPrefixCuts (2^48) 3709468673 9 Manual.Count131072.C028271.packed 128 cuts28271 = true := by
 decide +kernel
def pointBounds28271 : List (Nat × Nat × Nat) := [(3709543424,104471724598472,104472107495942)]
theorem point_links_checked28271 : (cuts28271.take 1).map (fun c => (3709468673-1+2*2^9*c.k,104471472830800+c.lower,104471855728122+c.upper)) = pointBounds28271 := by
 decide +kernel
def cuts28272 : List PrefixCut := [⟨59,205853816,205853930⟩,
⟨128,446379083,446379333⟩]
theorem checked28272 : checkPrefixCuts (2^48) 3709599745 9 Manual.Count131072.C028272.packed 128 cuts28272 = true := by
 decide +kernel
def pointBounds28272 : List (Nat × Nat × Nat) := [(3709660160,104472127962748,104472510860442)]
theorem point_links_checked28272 : (cuts28272.take 1).map (fun c => (3709599745-1+2*2^9*c.k,104471922108932+c.lower,104472305006512+c.upper)) = pointBounds28272 := by
 decide +kernel
def cuts28273 : List PrefixCut := [⟨45,160549977,160550065⟩,
⟨128,456150966,456151217⟩]
theorem checked28273 : checkPrefixCuts (2^48) 3709730817 9 Manual.Count131072.C028273.packed 128 cuts28273 = true := by
 decide +kernel
def pointBounds28273 : List (Nat × Nat × Nat) := [(3709776896,104472529037992,104472911935910)]
theorem point_links_checked28273 : (cuts28273.take 1).map (fun c => (3709730817-1+2*2^9*c.k,104472368488015+c.lower,104472751385845+c.upper)) = pointBounds28273 := by
 decide +kernel
def cuts28274 : List PrefixCut := [⟨31,110014036,110014096⟩,
⟨128,453706969,453707222⟩]
theorem checked28274 : checkPrefixCuts (2^48) 3709861889 9 Manual.Count131072.C028274.packed 128 cuts28274 = true := by
 decide +kernel
def pointBounds28274 : List (Nat × Nat × Nat) := [(3709893632,104472934653017,104473317551158)]
theorem point_links_checked28274 : (cuts28274.take 1).map (fun c => (3709861889-1+2*2^9*c.k,104472824638981+c.lower,104473207537062+c.upper)) = pointBounds28274 := by
 decide +kernel
def cuts28275 : List PrefixCut := [⟨17,60240151,60240184⟩,
⟨128,453235646,453235900⟩]
theorem checked28275 : checkPrefixCuts (2^48) 3709992961 9 Manual.Count131072.C028275.packed 128 cuts28275 = true := by
 decide +kernel
def pointBounds28275 : List (Nat × Nat × Nat) := [(3710010368,104473338586101,104473721484468)]
theorem point_links_checked28275 : (cuts28275.take 1).map (fun c => (3709992961-1+2*2^9*c.k,104473278345950+c.lower,104473661244284+c.upper)) = pointBounds28275 := by
 decide +kernel
def cuts28276 : List PrefixCut := [⟨3,10166135,10166141⟩,
⟨117,410432320,410432546⟩,
⟨128,448971306,448971553⟩]
theorem checked28276 : checkPrefixCuts (2^48) 3710124033 9 Manual.Count131072.C028276.packed 128 cuts28276 = true := by
 decide +kernel
def pointBounds28276 : List (Nat × Nat × Nat) := [(3710127104,104473741747731,104474124646325),(3710243840,104474142013916,104474524912730)]
theorem point_links_checked28276 : (cuts28276.take 2).map (fun c => (3710124033-1+2*2^9*c.k,104473731581596+c.lower,104474114480184+c.upper)) = pointBounds28276 := by
 decide +kernel
def cuts28277 : List PrefixCut := [⟨103,363535290,363535500⟩,
⟨128,452217507,452217766⟩]
theorem checked28277 : checkPrefixCuts (2^48) 3710255105 9 Manual.Count131072.C028277.packed 128 cuts28277 = true := by
 decide +kernel
def pointBounds28277 : List (Nat × Nat × Nat) := [(3710360576,104474544088192,104474926987237)]
theorem point_links_checked28277 : (cuts28277.take 1).map (fun c => (3710255105-1+2*2^9*c.k,104474180552902+c.lower,104474563451737+c.upper)) = pointBounds28277 := by
 decide +kernel
def cuts28278 : List PrefixCut := [⟨89,315427621,315427797⟩,
⟨128,454249741,454249993⟩]
theorem checked28278 : checkPrefixCuts (2^48) 3710386177 9 Manual.Count131072.C028278.packed 128 cuts28278 = true := by
 decide +kernel
def pointBounds28278 : List (Nat × Nat × Nat) := [(3710477312,104474948198030,104475331097300)]
theorem point_links_checked28278 : (cuts28278.take 1).map (fun c => (3710386177-1+2*2^9*c.k,104474632770409+c.lower,104475015669503+c.upper)) = pointBounds28278 := by
 decide +kernel
def cuts28279 : List PrefixCut := [⟨75,259282265,259282413⟩,
⟨128,445737643,445737896⟩]
theorem checked28279 : checkPrefixCuts (2^48) 3710517249 9 Manual.Count131072.C028279.packed 128 cuts28279 = true := by
 decide +kernel
def pointBounds28279 : List (Nat × Nat × Nat) := [(3710594048,104475346302415,104475729201909)]
theorem point_links_checked28279 : (cuts28279.take 1).map (fun c => (3710517249-1+2*2^9*c.k,104475087020150+c.lower,104475469919496+c.upper)) = pointBounds28279 := by
 decide +kernel
def cuts28280 : List PrefixCut := [⟨61,216946309,216946428⟩,
⟨128,453383281,453383530⟩]
theorem checked28280 : checkPrefixCuts (2^48) 3710648321 9 Manual.Count131072.C028280.packed 128 cuts28280 = true := by
 decide +kernel
def pointBounds28280 : List (Nat × Nat × Nat) := [(3710710784,104475749704102,104476132603820)]
theorem point_links_checked28280 : (cuts28280.take 1).map (fun c => (3710648321-1+2*2^9*c.k,104475532757793+c.lower,104475915657392+c.upper)) = pointBounds28280 := by
 decide +kernel
def cuts28281 : List PrefixCut := [⟨47,163917952,163918043⟩,
⟨128,448816130,448816382⟩]
theorem checked28281 : checkPrefixCuts (2^48) 3710779393 9 Manual.Count131072.C028281.packed 128 cuts28281 = true := by
 decide +kernel
def pointBounds28281 : List (Nat × Nat × Nat) := [(3710827520,104476150059026,104476532958965)]
theorem point_links_checked28281 : (cuts28281.take 1).map (fun c => (3710779393-1+2*2^9*c.k,104475986141074+c.lower,104476369040922+c.upper)) = pointBounds28281 := by
 decide +kernel
def cuts28282 : List PrefixCut := [⟨33,113851279,113851345⟩,
⟨128,445235342,445235594⟩]
theorem checked28282 : checkPrefixCuts (2^48) 3710910465 9 Manual.Count131072.C028282.packed 128 cuts28282 = true := by
 decide +kernel
def pointBounds28282 : List (Nat × Nat × Nat) := [(3710944256,104476548808483,104476931708649)]
theorem point_links_checked28282 : (cuts28282.take 1).map (fun c => (3710910465-1+2*2^9*c.k,104476434957204+c.lower,104476817857304+c.upper)) = pointBounds28282 := by
 decide +kernel
def cuts28283 : List PrefixCut := [⟨19,68793914,68793951⟩,
⟨128,453335304,453335554⟩]
theorem checked28283 : checkPrefixCuts (2^48) 3711041537 9 Manual.Count131072.C028283.packed 128 cuts28283 = true := by
 decide +kernel
def pointBounds28283 : List (Nat × Nat × Nat) := [(3711060992,104476948986460,104477331886849)]
theorem point_links_checked28283 : (cuts28283.take 1).map (fun c => (3711041537-1+2*2^9*c.k,104476880192546+c.lower,104477263092898+c.upper)) = pointBounds28283 := by
 decide +kernel
def cuts28284 : List PrefixCut := [⟨5,16230876,16230887⟩,
⟨119,416156193,416156426⟩,
⟨128,446796638,446796889⟩]
theorem checked28284 : checkPrefixCuts (2^48) 3711172609 9 Manual.Count131072.C028284.packed 128 cuts28284 = true := by
 decide +kernel
def pointBounds28284 : List (Nat × Nat × Nat) := [(3711177728,104477349758726,104477732659339),(3711294464,104477749684043,104478132584878)]
theorem point_links_checked28284 : (cuts28284.take 2).map (fun c => (3711172609-1+2*2^9*c.k,104477333527850+c.lower,104477716428452+c.upper)) = pointBounds28284 := by
 decide +kernel
def cuts28285 : List PrefixCut := [⟨105,366541927,366542129⟩,
⟨128,447918415,447918662⟩]
theorem checked28285 : checkPrefixCuts (2^48) 3711303681 9 Manual.Count131072.C028285.packed 128 cuts28285 = true := by
 decide +kernel
def pointBounds28285 : List (Nat × Nat × Nat) := [(3711411200,104478146866415,104478529767470)]
theorem point_links_checked28285 : (cuts28285.take 1).map (fun c => (3711303681-1+2*2^9*c.k,104477780324488+c.lower,104478163225341+c.upper)) = pointBounds28285 := by
 decide +kernel
def cuts28286 : List PrefixCut := [⟨91,319130357,319130538⟩,
⟨128,453059615,453059870⟩]
theorem checked28286 : checkPrefixCuts (2^48) 3711434753 9 Manual.Count131072.C028286.packed 128 cuts28286 = true := by
 decide +kernel
def pointBounds28286 : List (Nat × Nat × Nat) := [(3711527936,104478547373260,104478930274541)]
theorem point_links_checked28286 : (cuts28286.take 1).map (fun c => (3711434753-1+2*2^9*c.k,104478228242903+c.lower,104478611144003+c.upper)) = pointBounds28286 := by
 decide +kernel
def cuts28287 : List PrefixCut := [⟨77,271646113,271646267⟩,
⟨128,449934403,449934658⟩]
theorem checked28287 : checkPrefixCuts (2^48) 3711565825 9 Manual.Count131072.C028287.packed 128 cuts28287 = true := by
 decide +kernel
def pointBounds28287 : List (Nat × Nat × Nat) := [(3711644672,104478952948631,104479335850140)]
theorem point_links_checked28287 : (cuts28287.take 1).map (fun c => (3711565825-1+2*2^9*c.k,104478681302518+c.lower,104479064203873+c.upper)) = pointBounds28287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000258
