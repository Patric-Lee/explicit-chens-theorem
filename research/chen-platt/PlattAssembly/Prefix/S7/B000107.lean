import PlattAssemblyKernel
import PlattCertificates.Count131072.C063424
import PlattCertificates.Count131072.C063425
import PlattCertificates.Count131072.C063426
import PlattCertificates.Count131072.C063427
import PlattCertificates.Count131072.C063428
import PlattCertificates.Count131072.C063429
import PlattCertificates.Count131072.C063430
import PlattCertificates.Count131072.C063431
import PlattCertificates.Count131072.C063432
import PlattCertificates.Count131072.C063433
import PlattCertificates.Count131072.C063434
import PlattCertificates.Count131072.C063435
import PlattCertificates.Count131072.C063436
import PlattCertificates.Count131072.C063437
import PlattCertificates.Count131072.C063438
import PlattCertificates.Count131072.C063439
import PlattCertificates.Count131072.C063440
import PlattCertificates.Count131072.C063441
import PlattCertificates.Count131072.C063442
import PlattCertificates.Count131072.C063443
import PlattCertificates.Count131072.C063444
import PlattCertificates.Count131072.C063445
import PlattCertificates.Count131072.C063446
import PlattCertificates.Count131072.C063447
import PlattCertificates.Count131072.C063448
import PlattCertificates.Count131072.C063449
import PlattCertificates.Count131072.C063450
import PlattCertificates.Count131072.C063451
import PlattCertificates.Count131072.C063452
import PlattCertificates.Count131072.C063453
import PlattCertificates.Count131072.C063454
import PlattCertificates.Count131072.C063455
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63424 : List PrefixCut := [⟨64,192362932,192363040⟩]
theorem checked63424 : checkPrefixCuts (2^48) 8317042689 10 Manual.Count131072.C063424.packed 64 cuts63424 = true := by
 decide +kernel
def cuts63425 : List PrefixCut := [⟨7,20373237,20373247⟩,
⟨64,193882786,193882895⟩]
theorem checked63425 : checkPrefixCuts (2^48) 8317173761 10 Manual.Count131072.C063425.packed 64 cuts63425 = true := by
 decide +kernel
def pointBounds63425 : List (Nat × Nat × Nat) := [(8317188096,114601471555960,114601860355764)]
theorem point_links_checked63425 : (cuts63425.take 1).map (fun c => (8317173761-1+2*2^10*c.k,114601451182723+c.lower,114601839982517+c.upper)) = pointBounds63425 := by
 decide +kernel
def cuts63426 : List PrefixCut := [⟨64,193033696,193033810⟩]
theorem checked63426 : checkPrefixCuts (2^48) 8317304833 10 Manual.Count131072.C063426.packed 64 cuts63426 = true := by
 decide +kernel
def cuts63427 : List PrefixCut := [⟨6,18443630,18443640⟩,
⟨64,190763309,190763417⟩]
theorem checked63427 : checkPrefixCuts (2^48) 8317435905 10 Manual.Count131072.C063427.packed 64 cuts63427 = true := by
 decide +kernel
def pointBounds63427 : List (Nat × Nat × Nat) := [(8317448192,114601856542835,114602245342862)]
theorem point_links_checked63427 : (cuts63427.take 1).map (fun c => (8317435905-1+2*2^10*c.k,114601838099205+c.lower,114602226899222+c.upper)) = pointBounds63427 := by
 decide +kernel
def cuts63428 : List PrefixCut := [⟨64,190286526,190286633⟩]
theorem checked63428 : checkPrefixCuts (2^48) 8317566977 10 Manual.Count131072.C063428.packed 64 cuts63428 = true := by
 decide +kernel
def cuts63429 : List PrefixCut := [⟨5,14991323,14991332⟩,
⟨64,194919628,194919743⟩]
theorem checked63429 : checkPrefixCuts (2^48) 8317698049 10 Manual.Count131072.C063429.packed 64 cuts63429 = true := by
 decide +kernel
def pointBounds63429 : List (Nat × Nat × Nat) := [(8317708288,114602234140363,114602622940604)]
theorem point_links_checked63429 : (cuts63429.take 1).map (fun c => (8317698049-1+2*2^10*c.k,114602219149040+c.lower,114602607949272+c.upper)) = pointBounds63429 := by
 decide +kernel
def cuts63430 : List PrefixCut := [⟨64,193055377,193055492⟩]
theorem checked63430 : checkPrefixCuts (2^48) 8317829121 10 Manual.Count131072.C063430.packed 64 cuts63430 = true := by
 decide +kernel
def cuts63431 : List PrefixCut := [⟨4,12114505,12114511⟩,
⟨64,192680099,192680207⟩]
theorem checked63431 : checkPrefixCuts (2^48) 8317960193 10 Manual.Count131072.C063431.packed 64 cuts63431 = true := by
 decide +kernel
def pointBounds63431 : List (Nat × Nat × Nat) := [(8317968384,114602619238550,114603008039018)]
theorem point_links_checked63431 : (cuts63431.take 1).map (fun c => (8317960193-1+2*2^10*c.k,114602607124045+c.lower,114602995924507+c.upper)) = pointBounds63431 := by
 decide +kernel
def cuts63432 : List PrefixCut := [⟨64,193759914,193760025⟩]
theorem checked63432 : checkPrefixCuts (2^48) 8318091265 10 Manual.Count131072.C063432.packed 64 cuts63432 = true := by
 decide +kernel
def cuts63433 : List PrefixCut := [⟨3,8391906,8391912⟩,
⟨64,195313397,195313507⟩]
theorem checked63433 : checkPrefixCuts (2^48) 8318222337 10 Manual.Count131072.C063433.packed 64 cuts63433 = true := by
 decide +kernel
def pointBounds63433 : List (Nat × Nat × Nat) := [(8318228480,114603001955964,114603390756651)]
theorem point_links_checked63433 : (cuts63433.take 1).map (fun c => (8318222337-1+2*2^10*c.k,114602993564058+c.lower,114603382364739+c.upper)) = pointBounds63433 := by
 decide +kernel
def cuts63434 : List PrefixCut := [⟨64,194701253,194701366⟩]
theorem checked63434 : checkPrefixCuts (2^48) 8318353409 10 Manual.Count131072.C063434.packed 64 cuts63434 = true := by
 decide +kernel
def cuts63435 : List PrefixCut := [⟨2,5481638,5481642⟩,
⟨64,195950140,195950255⟩]
theorem checked63435 : checkPrefixCuts (2^48) 8318484481 10 Manual.Count131072.C063435.packed 64 cuts63435 = true := by
 decide +kernel
def pointBounds63435 : List (Nat × Nat × Nat) := [(8318488576,114603389060346,114603777861254)]
theorem point_links_checked63435 : (cuts63435.take 1).map (fun c => (8318484481-1+2*2^10*c.k,114603383578708+c.lower,114603772379612+c.upper)) = pointBounds63435 := by
 decide +kernel
def cuts63436 : List PrefixCut := [⟨64,192766422,192766540⟩]
theorem checked63436 : checkPrefixCuts (2^48) 8318615553 10 Manual.Count131072.C063436.packed 64 cuts63436 = true := by
 decide +kernel
def cuts63437 : List PrefixCut := [⟨1,2605388,2605390⟩,
⟨64,195131907,195132011⟩]
theorem checked63437 : checkPrefixCuts (2^48) 8318746625 10 Manual.Count131072.C063437.packed 64 cuts63437 = true := by
 decide +kernel
def pointBounds63437 : List (Nat × Nat × Nat) := [(8318748672,114603774900658,114604163701797)]
theorem point_links_checked63437 : (cuts63437.take 1).map (fun c => (8318746625-1+2*2^10*c.k,114603772295270+c.lower,114604161096407+c.upper)) = pointBounds63437 := by
 decide +kernel
def cuts63438 : List PrefixCut := [⟨64,195771721,195771831⟩]
theorem checked63438 : checkPrefixCuts (2^48) 8318877697 10 Manual.Count131072.C063438.packed 64 cuts63438 = true := by
 decide +kernel
def pointBounds63438 : List (Nat × Nat × Nat) := [(8319008768,114604163198898,114604552000249)]
theorem point_links_checked63438 : (cuts63438.take 1).map (fun c => (8318877697-1+2*2^10*c.k,114603967427177+c.lower,114604356228418+c.upper)) = pointBounds63438 := by
 decide +kernel
def cuts63439 : List PrefixCut := [⟨64,194685922,194686035⟩]
theorem checked63439 : checkPrefixCuts (2^48) 8319008769 10 Manual.Count131072.C063439.packed 64 cuts63439 = true := by
 decide +kernel
def cuts63440 : List PrefixCut := [⟨63,194446025,194446134⟩,
⟨64,197829434,197829545⟩]
theorem checked63440 : checkPrefixCuts (2^48) 8319139841 10 Manual.Count131072.C063440.packed 64 cuts63440 = true := by
 decide +kernel
def pointBounds63440 : List (Nat × Nat × Nat) := [(8319268864,114604552330845,114604941132418)]
theorem point_links_checked63440 : (cuts63440.take 1).map (fun c => (8319139841-1+2*2^10*c.k,114604357884820+c.lower,114604746686284+c.upper)) = pointBounds63440 := by
 decide +kernel
def cuts63441 : List PrefixCut := [⟨64,192006882,192006997⟩]
theorem checked63441 : checkPrefixCuts (2^48) 8319270913 10 Manual.Count131072.C063441.packed 64 cuts63441 = true := by
 decide +kernel
def cuts63442 : List PrefixCut := [⟨62,188045423,188045525⟩,
⟨64,194203034,194203139⟩]
theorem checked63442 : checkPrefixCuts (2^48) 8319401985 10 Manual.Count131072.C063442.packed 64 cuts63442 = true := by
 decide +kernel
def pointBounds63442 : List (Nat × Nat × Nat) := [(8319528960,114604935766559,114605324568351)]
theorem point_links_checked63442 : (cuts63442.take 1).map (fun c => (8319401985-1+2*2^10*c.k,114604747721136+c.lower,114605136522826+c.upper)) = pointBounds63442 := by
 decide +kernel
def cuts63443 : List PrefixCut := [⟨64,194741318,194741428⟩]
theorem checked63443 : checkPrefixCuts (2^48) 8319533057 10 Manual.Count131072.C063443.packed 64 cuts63443 = true := by
 decide +kernel
def cuts63444 : List PrefixCut := [⟨61,185671273,185671383⟩,
⟨64,193689448,193689562⟩]
theorem checked63444 : checkPrefixCuts (2^48) 8319664129 10 Manual.Count131072.C063444.packed 64 cuts63444 = true := by
 decide +kernel
def pointBounds63444 : List (Nat × Nat × Nat) := [(8319789056,114605322336761,114605711138776)]
theorem point_links_checked63444 : (cuts63444.take 1).map (fun c => (8319664129-1+2*2^10*c.k,114605136665488+c.lower,114605525467393+c.upper)) = pointBounds63444 := by
 decide +kernel
def cuts63445 : List PrefixCut := [⟨64,195174973,195175084⟩]
theorem checked63445 : checkPrefixCuts (2^48) 8319795201 10 Manual.Count131072.C063445.packed 64 cuts63445 = true := by
 decide +kernel
def cuts63446 : List PrefixCut := [⟨60,182383822,182383927⟩,
⟨64,195442550,195442662⟩]
theorem checked63446 : checkPrefixCuts (2^48) 8319926273 10 Manual.Count131072.C063446.packed 64 cuts63446 = true := by
 decide +kernel
def pointBounds63446 : List (Nat × Nat × Nat) := [(8320049152,114605707913731,114606096715966)]
theorem point_links_checked63446 : (cuts63446.take 1).map (fun c => (8319926273-1+2*2^10*c.k,114605525529909+c.lower,114605914332039+c.upper)) = pointBounds63446 := by
 decide +kernel
def cuts63447 : List PrefixCut := [⟨64,191921099,191921204⟩]
theorem checked63447 : checkPrefixCuts (2^48) 8320057345 10 Manual.Count131072.C063447.packed 64 cuts63447 = true := by
 decide +kernel
def cuts63448 : List PrefixCut := [⟨59,178487641,178487742⟩,
⟨64,193135961,193136070⟩]
theorem checked63448 : checkPrefixCuts (2^48) 8320188417 10 Manual.Count131072.C063448.packed 64 cuts63448 = true := by
 decide +kernel
def pointBounds63448 : List (Nat × Nat × Nat) := [(8320309248,114606091381199,114606480183647)]
theorem point_links_checked63448 : (cuts63448.take 1).map (fun c => (8320188417-1+2*2^10*c.k,114605912893558+c.lower,114606301695905+c.upper)) = pointBounds63448 := by
 decide +kernel
def cuts63449 : List PrefixCut := [⟨64,194012464,194012578⟩]
theorem checked63449 : checkPrefixCuts (2^48) 8320319489 10 Manual.Count131072.C063449.packed 64 cuts63449 = true := by
 decide +kernel
def cuts63450 : List PrefixCut := [⟨58,175911033,175911132⟩,
⟨64,193806455,193806565⟩]
theorem checked63450 : checkPrefixCuts (2^48) 8320450561 10 Manual.Count131072.C063450.packed 64 cuts63450 = true := by
 decide +kernel
def pointBounds63450 : List (Nat × Nat × Nat) := [(8320569344,114606475953016,114606864755685)]
theorem point_links_checked63450 : (cuts63450.take 1).map (fun c => (8320450561-1+2*2^10*c.k,114606300041983+c.lower,114606688844553+c.upper)) = pointBounds63450 := by
 decide +kernel
def cuts63451 : List PrefixCut := [⟨64,193160665,193160774⟩]
theorem checked63451 : checkPrefixCuts (2^48) 8320581633 10 Manual.Count131072.C063451.packed 64 cuts63451 = true := by
 decide +kernel
def cuts63452 : List PrefixCut := [⟨57,174146456,174146551⟩,
⟨64,195322606,195322713⟩]
theorem checked63452 : checkPrefixCuts (2^48) 8320712705 10 Manual.Count131072.C063452.packed 64 cuts63452 = true := by
 decide +kernel
def pointBounds63452 : List (Nat × Nat × Nat) := [(8320829440,114606861155559,114607249958443)]
theorem point_links_checked63452 : (cuts63452.take 1).map (fun c => (8320712705-1+2*2^10*c.k,114606687009103+c.lower,114607075811892+c.upper)) = pointBounds63452 := by
 decide +kernel
def cuts63453 : List PrefixCut := [⟨64,193492846,193492956⟩]
theorem checked63453 : checkPrefixCuts (2^48) 8320843777 10 Manual.Count131072.C063453.packed 64 cuts63453 = true := by
 decide +kernel
def cuts63454 : List PrefixCut := [⟨56,170724467,170724571⟩,
⟨64,193422153,193422269⟩]
theorem checked63454 : checkPrefixCuts (2^48) 8320974849 10 Manual.Count131072.C063454.packed 64 cuts63454 = true := by
 decide +kernel
def pointBounds63454 : List (Nat × Nat × Nat) := [(8321089536,114607246549022,114607635352132)]
theorem point_links_checked63454 : (cuts63454.take 1).map (fun c => (8320974849-1+2*2^10*c.k,114607075824555+c.lower,114607464627561+c.upper)) = pointBounds63454 := by
 decide +kernel
def cuts63455 : List PrefixCut := [⟨64,192810217,192810330⟩]
theorem checked63455 : checkPrefixCuts (2^48) 8321105921 10 Manual.Count131072.C063455.packed 64 cuts63455 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000107
