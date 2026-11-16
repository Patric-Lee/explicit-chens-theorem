import PlattAssemblyKernel
import PlattCertificates.Count131072.C050416
import PlattCertificates.Count131072.C050417
import PlattCertificates.Count131072.C050418
import PlattCertificates.Count131072.C050419
import PlattCertificates.Count131072.C050420
import PlattCertificates.Count131072.C050421
import PlattCertificates.Count131072.C050422
import PlattCertificates.Count131072.C050423
import PlattCertificates.Count131072.C050424
import PlattCertificates.Count131072.C050425
import PlattCertificates.Count131072.C050426
import PlattCertificates.Count131072.C050427
import PlattCertificates.Count131072.C050428
import PlattCertificates.Count131072.C050429
import PlattCertificates.Count131072.C050430
import PlattCertificates.Count131072.C050431
import PlattCertificates.Count131072.C050432
import PlattCertificates.Count131072.C050433
import PlattCertificates.Count131072.C050434
import PlattCertificates.Count131072.C050435
import PlattCertificates.Count131072.C050436
import PlattCertificates.Count131072.C050437
import PlattCertificates.Count131072.C050438
import PlattCertificates.Count131072.C050439
import PlattCertificates.Count131072.C050440
import PlattCertificates.Count131072.C050441
import PlattCertificates.Count131072.C050442
import PlattCertificates.Count131072.C050443
import PlattCertificates.Count131072.C050444
import PlattCertificates.Count131072.C050445
import PlattCertificates.Count131072.C050446
import PlattCertificates.Count131072.C050447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50416 : List PrefixCut := [⟨52,201056175,201056295⟩,
⟨64,248818786,248818933⟩]
theorem checked50416 : checkPrefixCuts (2^48) 6612058113 10 Manual.Count131072.C050416.packed 64 cuts50416 = true := by
 decide +kernel
def pointBounds50416 : List (Nat × Nat × Nat) := [(6612164608,111760171896919,111760559077779)]
theorem point_links_checked50416 : (cuts50416.take 1).map (fun c => (6612058113-1+2*2^10*c.k,111759970840744+c.lower,111760358021484+c.upper)) = pointBounds50416 := by
 decide +kernel
def cuts50417 : List PrefixCut := [⟨64,247238847,247238986⟩]
theorem checked50417 : checkPrefixCuts (2^48) 6612189185 10 Manual.Count131072.C050417.packed 64 cuts50417 = true := by
 decide +kernel
def cuts50418 : List PrefixCut := [⟨25,95054534,95054588⟩,
⟨64,247617024,247617166⟩]
theorem checked50418 : checkPrefixCuts (2^48) 6612320257 10 Manual.Count131072.C050418.packed 64 cuts50418 = true := by
 decide +kernel
def pointBounds50418 : List (Nat × Nat × Nat) := [(6612371456,111760561952911,111760949133991)]
theorem point_links_checked50418 : (cuts50418.take 1).map (fun c => (6612320257-1+2*2^10*c.k,111760466898377+c.lower,111760854079403+c.upper)) = pointBounds50418 := by
 decide +kernel
def cuts50419 : List PrefixCut := [⟨62,234459016,234459153⟩,
⟨64,241823033,241823174⟩]
theorem checked50419 : checkPrefixCuts (2^48) 6612451329 10 Manual.Count131072.C050419.packed 64 cuts50419 = true := by
 decide +kernel
def pointBounds50419 : List (Nat × Nat × Nat) := [(6612578304,111760948974417,111761336155722)]
theorem point_links_checked50419 : (cuts50419.take 1).map (fun c => (6612451329-1+2*2^10*c.k,111760714515401+c.lower,111761101696569+c.upper)) = pointBounds50419 := by
 decide +kernel
def cuts50420 : List PrefixCut := [⟨64,251778700,251778847⟩]
theorem checked50420 : checkPrefixCuts (2^48) 6612582401 10 Manual.Count131072.C050420.packed 64 cuts50420 = true := by
 decide +kernel
def cuts50421 : List PrefixCut := [⟨35,135741342,135741418⟩,
⟨64,247432076,247432214⟩]
theorem checked50421 : checkPrefixCuts (2^48) 6612713473 10 Manual.Count131072.C050421.packed 64 cuts50421 = true := by
 decide +kernel
def pointBounds50421 : List (Nat × Nat × Nat) := [(6612785152,111761343858476,111761731040008)]
theorem point_links_checked50421 : (cuts50421.take 1).map (fun c => (6612713473-1+2*2^10*c.k,111761208117134+c.lower,111761595298590+c.upper)) = pointBounds50421 := by
 decide +kernel
def cuts50422 : List PrefixCut := [⟨64,246746131,246746265⟩]
theorem checked50422 : checkPrefixCuts (2^48) 6612844545 10 Manual.Count131072.C050422.packed 64 cuts50422 = true := by
 decide +kernel
def cuts50423 : List PrefixCut := [⟨8,30050168,30050186⟩,
⟨64,243846913,243847056⟩]
theorem checked50423 : checkPrefixCuts (2^48) 6612975617 10 Manual.Count131072.C050423.packed 64 cuts50423 = true := by
 decide +kernel
def pointBounds50423 : List (Nat × Nat × Nat) := [(6612992000,111761732345509,111762119527255)]
theorem point_links_checked50423 : (cuts50423.take 1).map (fun c => (6612975617-1+2*2^10*c.k,111761702295341+c.lower,111762089477069+c.upper)) = pointBounds50423 := by
 decide +kernel
def cuts50424 : List PrefixCut := [⟨45,174039667,174039766⟩,
⟨64,246821489,246821628⟩]
theorem checked50424 : checkPrefixCuts (2^48) 6613106689 10 Manual.Count131072.C050424.packed 64 cuts50424 = true := by
 decide +kernel
def pointBounds50424 : List (Nat × Nat × Nat) := [(6613198848,111762120181921,111762507363891)]
theorem point_links_checked50424 : (cuts50424.take 1).map (fun c => (6613106689-1+2*2^10*c.k,111761946142254+c.lower,111762333324125+c.upper)) = pointBounds50424 := by
 decide +kernel
def cuts50425 : List PrefixCut := [⟨64,244773603,244773745⟩]
theorem checked50425 : checkPrefixCuts (2^48) 6613237761 10 Manual.Count131072.C050425.packed 64 cuts50425 = true := by
 decide +kernel
def cuts50426 : List PrefixCut := [⟨18,72098979,72099019⟩,
⟨64,250855016,250855153⟩]
theorem checked50426 : checkPrefixCuts (2^48) 6613368833 10 Manual.Count131072.C050426.packed 64 cuts50426 = true := by
 decide +kernel
def pointBounds50426 : List (Nat × Nat × Nat) := [(6613405696,111762509836325,111762897018517)]
theorem point_links_checked50426 : (cuts50426.take 1).map (fun c => (6613368833-1+2*2^10*c.k,111762437737346+c.lower,111762824919498+c.upper)) = pointBounds50426 := by
 decide +kernel
def cuts50427 : List PrefixCut := [⟨55,209524326,209524451⟩,
⟨64,243274306,243274450⟩]
theorem checked50427 : checkPrefixCuts (2^48) 6613499905 10 Manual.Count131072.C050427.packed 64 cuts50427 = true := by
 decide +kernel
def pointBounds50427 : List (Nat × Nat × Nat) := [(6613612544,111762898116688,111763285299102)]
theorem point_links_checked50427 : (cuts50427.take 1).map (fun c => (6613499905-1+2*2^10*c.k,111762688592362+c.lower,111763075774651+c.upper)) = pointBounds50427 := by
 decide +kernel
def cuts50428 : List PrefixCut := [⟨64,247908453,247908593⟩]
theorem checked50428 : checkPrefixCuts (2^48) 6613630977 10 Manual.Count131072.C050428.packed 64 cuts50428 = true := by
 decide +kernel
def cuts50429 : List PrefixCut := [⟨28,107588608,107588668⟩,
⟨64,247477946,247478087⟩]
theorem checked50429 : checkPrefixCuts (2^48) 6613762049 10 Manual.Count131072.C050429.packed 64 cuts50429 = true := by
 decide +kernel
def pointBounds50429 : List (Nat × Nat × Nat) := [(6613819392,111763287363729,111763674546362)]
theorem point_links_checked50429 : (cuts50429.take 1).map (fun c => (6613762049-1+2*2^10*c.k,111763179775121+c.lower,111763566957694+c.upper)) = pointBounds50429 := by
 decide +kernel
def cuts50430 : List PrefixCut := [⟨64,248451880,248452023⟩]
theorem checked50430 : checkPrefixCuts (2^48) 6613893121 10 Manual.Count131072.C050430.packed 64 cuts50430 = true := by
 decide +kernel
def cuts50431 : List PrefixCut := [⟨1,4042941,4042943⟩,
⟨64,245084962,245085102⟩]
theorem checked50431 : checkPrefixCuts (2^48) 6614024193 10 Manual.Count131072.C050431.packed 64 cuts50431 = true := by
 decide +kernel
def pointBounds50431 : List (Nat × Nat × Nat) := [(6614026240,111763679747888,111764066930747)]
theorem point_links_checked50431 : (cuts50431.take 1).map (fun c => (6614024193-1+2*2^10*c.k,111763675704947+c.lower,111764062887804+c.upper)) = pointBounds50431 := by
 decide +kernel
def cuts50432 : List PrefixCut := [⟨38,148946662,148946747⟩,
⟨64,246016363,246016507⟩]
theorem checked50432 : checkPrefixCuts (2^48) 6614155265 10 Manual.Count131072.C050432.packed 64 cuts50432 = true := by
 decide +kernel
def pointBounds50432 : List (Nat × Nat × Nat) := [(6614233088,111764069736571,111764456919653)]
theorem point_links_checked50432 : (cuts50432.take 1).map (fun c => (6614155265-1+2*2^10*c.k,111763920789909+c.lower,111764307972906+c.upper)) = pointBounds50432 := by
 decide +kernel
def cuts50433 : List PrefixCut := [⟨64,244522024,244522160⟩]
theorem checked50433 : checkPrefixCuts (2^48) 6614286337 10 Manual.Count131072.C050433.packed 64 cuts50433 = true := by
 decide +kernel
def cuts50434 : List PrefixCut := [⟨11,40767382,40767405⟩,
⟨64,245708680,245708820⟩]
theorem checked50434 : checkPrefixCuts (2^48) 6614417409 10 Manual.Count131072.C050434.packed 64 cuts50434 = true := by
 decide +kernel
def pointBounds50434 : List (Nat × Nat × Nat) := [(6614439936,111764452095678,111764839278978)]
theorem point_links_checked50434 : (cuts50434.take 1).map (fun c => (6614417409-1+2*2^10*c.k,111764411328296+c.lower,111764798511573+c.upper)) = pointBounds50434 := by
 decide +kernel
def cuts50435 : List PrefixCut := [⟨48,187491122,187491231⟩,
⟨64,251788964,251789109⟩]
theorem checked50435 : checkPrefixCuts (2^48) 6614548481 10 Manual.Count131072.C050435.packed 64 cuts50435 = true := by
 decide +kernel
def pointBounds50435 : List (Nat × Nat × Nat) := [(6614646784,111764844528098,111765231711624)]
theorem point_links_checked50435 : (cuts50435.take 1).map (fun c => (6614548481-1+2*2^10*c.k,111764657036976+c.lower,111765044220393+c.upper)) = pointBounds50435 := by
 decide +kernel
def cuts50436 : List PrefixCut := [⟨64,243741542,243741684⟩]
theorem checked50436 : checkPrefixCuts (2^48) 6614679553 10 Manual.Count131072.C050436.packed 64 cuts50436 = true := by
 decide +kernel
def cuts50437 : List PrefixCut := [⟨21,83572297,83572345⟩,
⟨64,249608891,249609034⟩]
theorem checked50437 : checkPrefixCuts (2^48) 6614810625 10 Manual.Count131072.C050437.packed 64 cuts50437 = true := by
 decide +kernel
def pointBounds50437 : List (Nat × Nat × Nat) := [(6614853632,111765236139779,111765623323531)]
theorem point_links_checked50437 : (cuts50437.take 1).map (fun c => (6614810625-1+2*2^10*c.k,111765152567482+c.lower,111765539751186+c.upper)) = pointBounds50437 := by
 decide +kernel
def cuts50438 : List PrefixCut := [⟨58,222243852,222243975⟩,
⟨64,245476467,245476602⟩]
theorem checked50438 : checkPrefixCuts (2^48) 6614941697 10 Manual.Count131072.C050438.packed 64 cuts50438 = true := by
 decide +kernel
def pointBounds50438 : List (Nat × Nat × Nat) := [(6615060480,111765624420225,111766011604195)]
theorem point_links_checked50438 : (cuts50438.take 1).map (fun c => (6614941697-1+2*2^10*c.k,111765402176373+c.lower,111765789360220+c.upper)) = pointBounds50438 := by
 decide +kernel
def cuts50439 : List PrefixCut := [⟨64,246663033,246663180⟩]
theorem checked50439 : checkPrefixCuts (2^48) 6615072769 10 Manual.Count131072.C050439.packed 64 cuts50439 = true := by
 decide +kernel
def cuts50440 : List PrefixCut := [⟨31,118585427,118585493⟩,
⟨64,243509492,243509627⟩]
theorem checked50440 : checkPrefixCuts (2^48) 6615203841 10 Manual.Count131072.C050440.packed 64 cuts50440 = true := by
 decide +kernel
def pointBounds50440 : List (Nat × Nat × Nat) := [(6615267328,111766012901300,111766400085495)]
theorem point_links_checked50440 : (cuts50440.take 1).map (fun c => (6615203841-1+2*2^10*c.k,111765894315873+c.lower,111766281500002+c.upper)) = pointBounds50440 := by
 decide +kernel
def cuts50441 : List PrefixCut := [⟨64,244951322,244951461⟩]
theorem checked50441 : checkPrefixCuts (2^48) 6615334913 10 Manual.Count131072.C050441.packed 64 cuts50441 = true := by
 decide +kernel
def cuts50442 : List PrefixCut := [⟨4,15487465,15487474⟩,
⟨64,248563012,248563147⟩]
theorem checked50442 : checkPrefixCuts (2^48) 6615465985 10 Manual.Count131072.C050442.packed 64 cuts50442 = true := by
 decide +kernel
def pointBounds50442 : List (Nat × Nat × Nat) := [(6615474176,111766398264152,111766785448564)]
theorem point_links_checked50442 : (cuts50442.take 1).map (fun c => (6615465985-1+2*2^10*c.k,111766382776687+c.lower,111766769961090+c.upper)) = pointBounds50442 := by
 decide +kernel
def cuts50443 : List PrefixCut := [⟨41,157891522,157891612⟩,
⟨64,246941291,246941431⟩]
theorem checked50443 : checkPrefixCuts (2^48) 6615597057 10 Manual.Count131072.C050443.packed 64 cuts50443 = true := by
 decide +kernel
def pointBounds50443 : List (Nat × Nat × Nat) := [(6615681024,111766789231221,111767176415849)]
theorem point_links_checked50443 : (cuts50443.take 1).map (fun c => (6615597057-1+2*2^10*c.k,111766631339699+c.lower,111767018524237+c.upper)) = pointBounds50443 := by
 decide +kernel
def cuts50444 : List PrefixCut := [⟨64,245362213,245362347⟩]
theorem checked50444 : checkPrefixCuts (2^48) 6615728129 10 Manual.Count131072.C050444.packed 64 cuts50444 = true := by
 decide +kernel
def cuts50445 : List PrefixCut := [⟨14,55351548,55351578⟩,
⟨64,247356980,247357120⟩]
theorem checked50445 : checkPrefixCuts (2^48) 6615859201 10 Manual.Count131072.C050445.packed 64 cuts50445 = true := by
 decide +kernel
def pointBounds50445 : List (Nat × Nat × Nat) := [(6615887872,111767178994751,111767566179593)]
theorem point_links_checked50445 : (cuts50445.take 1).map (fun c => (6615859201-1+2*2^10*c.k,111767123643203+c.lower,111767510828015+c.upper)) = pointBounds50445 := by
 decide +kernel
def cuts50446 : List PrefixCut := [⟨51,197107740,197107851⟩,
⟨64,245565216,245565354⟩]
theorem checked50446 : checkPrefixCuts (2^48) 6615990273 10 Manual.Count131072.C050446.packed 64 cuts50446 = true := by
 decide +kernel
def pointBounds50446 : List (Nat × Nat × Nat) := [(6616094720,111767568107923,111767955292986)]
theorem point_links_checked50446 : (cuts50446.take 1).map (fun c => (6615990273-1+2*2^10*c.k,111767371000183+c.lower,111767758185135+c.upper)) = pointBounds50446 := by
 decide +kernel
def cuts50447 : List PrefixCut := [⟨64,245687961,245688102⟩]
theorem checked50447 : checkPrefixCuts (2^48) 6616121345 10 Manual.Count131072.C050447.packed 64 cuts50447 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000013
