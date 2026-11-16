import PlattAssemblyKernel
import PlattCertificates.Count131072.C062432
import PlattCertificates.Count131072.C062433
import PlattCertificates.Count131072.C062434
import PlattCertificates.Count131072.C062435
import PlattCertificates.Count131072.C062436
import PlattCertificates.Count131072.C062437
import PlattCertificates.Count131072.C062438
import PlattCertificates.Count131072.C062439
import PlattCertificates.Count131072.C062440
import PlattCertificates.Count131072.C062441
import PlattCertificates.Count131072.C062442
import PlattCertificates.Count131072.C062443
import PlattCertificates.Count131072.C062444
import PlattCertificates.Count131072.C062445
import PlattCertificates.Count131072.C062446
import PlattCertificates.Count131072.C062447
import PlattCertificates.Count131072.C062448
import PlattCertificates.Count131072.C062449
import PlattCertificates.Count131072.C062450
import PlattCertificates.Count131072.C062451
import PlattCertificates.Count131072.C062452
import PlattCertificates.Count131072.C062453
import PlattCertificates.Count131072.C062454
import PlattCertificates.Count131072.C062455
import PlattCertificates.Count131072.C062456
import PlattCertificates.Count131072.C062457
import PlattCertificates.Count131072.C062458
import PlattCertificates.Count131072.C062459
import PlattCertificates.Count131072.C062460
import PlattCertificates.Count131072.C062461
import PlattCertificates.Count131072.C062462
import PlattCertificates.Count131072.C062463
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62432 : List PrefixCut := [⟨64,194764715,194764830⟩]
theorem checked62432 : checkPrefixCuts (2^48) 8187019265 10 Manual.Count131072.C062432.packed 64 cuts62432 = true := by
 decide +kernel
def cuts62433 : List PrefixCut := [⟨33,99976861,99976918⟩,
⟨64,194555317,194555434⟩]
theorem checked62433 : checkPrefixCuts (2^48) 8187150337 10 Manual.Count131072.C062433.packed 64 cuts62433 = true := by
 decide +kernel
def pointBounds62433 : List (Nat × Nat × Nat) := [(8187217920,114407258012811,114407646700896)]
theorem point_links_checked62433 : (cuts62433.take 1).map (fun c => (8187150337-1+2*2^10*c.k,114407158035950+c.lower,114407546723978+c.upper)) = pointBounds62433 := by
 decide +kernel
def cuts62434 : List PrefixCut := [⟨64,198712090,198712203⟩]
theorem checked62434 : checkPrefixCuts (2^48) 8187281409 10 Manual.Count131072.C062434.packed 64 cuts62434 = true := by
 decide +kernel
def cuts62435 : List PrefixCut := [⟨30,92926035,92926086⟩,
⟨64,195580464,195580576⟩]
theorem checked62435 : checkPrefixCuts (2^48) 8187412481 10 Manual.Count131072.C062435.packed 64 cuts62435 = true := by
 decide +kernel
def pointBounds62435 : List (Nat × Nat × Nat) := [(8187473920,114407644229392,114408032917701)]
theorem point_links_checked62435 : (cuts62435.take 1).map (fun c => (8187412481-1+2*2^10*c.k,114407551303357+c.lower,114407939991615+c.upper)) = pointBounds62435 := by
 decide +kernel
def cuts62436 : List PrefixCut := [⟨64,201524751,201524866⟩]
theorem checked62436 : checkPrefixCuts (2^48) 8187543553 10 Manual.Count131072.C062436.packed 64 cuts62436 = true := by
 decide +kernel
def cuts62437 : List PrefixCut := [⟨27,82609766,82609815⟩,
⟨64,196124236,196124350⟩]
theorem checked62437 : checkPrefixCuts (2^48) 8187674625 10 Manual.Count131072.C062437.packed 64 cuts62437 = true := by
 decide +kernel
def pointBounds62437 : List (Nat × Nat × Nat) := [(8187729920,114408031018338,114408419706872)]
theorem point_links_checked62437 : (cuts62437.take 1).map (fun c => (8187674625-1+2*2^10*c.k,114407948408572+c.lower,114408337097057+c.upper)) = pointBounds62437 := by
 decide +kernel
def cuts62438 : List PrefixCut := [⟨64,198974379,198974499⟩]
theorem checked62438 : checkPrefixCuts (2^48) 8187805697 10 Manual.Count131072.C062438.packed 64 cuts62438 = true := by
 decide +kernel
def cuts62439 : List PrefixCut := [⟨24,74734890,74734933⟩,
⟨64,198833691,198833805⟩]
theorem checked62439 : checkPrefixCuts (2^48) 8187936769 10 Manual.Count131072.C062439.packed 64 cuts62439 = true := by
 decide +kernel
def pointBounds62439 : List (Nat × Nat × Nat) := [(8187985920,114408418242077,114408806930839)]
theorem point_links_checked62439 : (cuts62439.take 1).map (fun c => (8187936769-1+2*2^10*c.k,114408343507187+c.lower,114408732195906+c.upper)) = pointBounds62439 := by
 decide +kernel
def cuts62440 : List PrefixCut := [⟨64,197971125,197971232⟩]
theorem checked62440 : checkPrefixCuts (2^48) 8188067841 10 Manual.Count131072.C062440.packed 64 cuts62440 = true := by
 decide +kernel
def cuts62441 : List PrefixCut := [⟨21,66069885,66069918⟩,
⟨64,197692965,197693073⟩]
theorem checked62441 : checkPrefixCuts (2^48) 8188198913 10 Manual.Count131072.C062441.packed 64 cuts62441 = true := by
 decide +kernel
def pointBounds62441 : List (Nat × Nat × Nat) := [(8188241920,114408806381888,114409195070861)]
theorem point_links_checked62441 : (cuts62441.take 1).map (fun c => (8188198913-1+2*2^10*c.k,114408740312003+c.lower,114409129000943+c.upper)) = pointBounds62441 := by
 decide +kernel
def cuts62442 : List PrefixCut := [⟨64,198136658,198136770⟩]
theorem checked62442 : checkPrefixCuts (2^48) 8188329985 10 Manual.Count131072.C062442.packed 64 cuts62442 = true := by
 decide +kernel
def cuts62443 : List PrefixCut := [⟨18,54999202,54999232⟩,
⟨64,195280417,195280534⟩]
theorem checked62443 : checkPrefixCuts (2^48) 8188461057 10 Manual.Count131072.C062443.packed 64 cuts62443 = true := by
 decide +kernel
def pointBounds62443 : List (Nat × Nat × Nat) := [(8188497920,114409191140828,114409579830018)]
theorem point_links_checked62443 : (cuts62443.take 1).map (fun c => (8188461057-1+2*2^10*c.k,114409136141626+c.lower,114409524830786+c.upper)) = pointBounds62443 := by
 decide +kernel
def cuts62444 : List PrefixCut := [⟨64,197855324,197855437⟩]
theorem checked62444 : checkPrefixCuts (2^48) 8188592129 10 Manual.Count131072.C062444.packed 64 cuts62444 = true := by
 decide +kernel
def cuts62445 : List PrefixCut := [⟨15,45785386,45785413⟩,
⟨64,196683456,196683570⟩]
theorem checked62445 : checkPrefixCuts (2^48) 8188723201 10 Manual.Count131072.C062445.packed 64 cuts62445 = true := by
 decide +kernel
def pointBounds62445 : List (Nat × Nat × Nat) := [(8188753920,114409575062753,114409963752170)]
theorem point_links_checked62445 : (cuts62445.take 1).map (fun c => (8188723201-1+2*2^10*c.k,114409529277367+c.lower,114409917966757+c.upper)) = pointBounds62445 := by
 decide +kernel
def cuts62446 : List PrefixCut := [⟨64,200461299,200461418⟩]
theorem checked62446 : checkPrefixCuts (2^48) 8188854273 10 Manual.Count131072.C062446.packed 64 cuts62446 = true := by
 decide +kernel
def cuts62447 : List PrefixCut := [⟨12,37190855,37190877⟩,
⟨64,195852238,195852355⟩]
theorem checked62447 : checkPrefixCuts (2^48) 8188985345 10 Manual.Count131072.C062447.packed 64 cuts62447 = true := by
 decide +kernel
def pointBounds62447 : List (Nat × Nat × Nat) := [(8189009920,114409963612977,114410352302622)]
theorem point_links_checked62447 : (cuts62447.take 1).map (fun c => (8188985345-1+2*2^10*c.k,114409926422122+c.lower,114410315111745+c.upper)) = pointBounds62447 := by
 decide +kernel
def cuts62448 : List PrefixCut := [⟨64,199320620,199320733⟩]
theorem checked62448 : checkPrefixCuts (2^48) 8189116417 10 Manual.Count131072.C062448.packed 64 cuts62448 = true := by
 decide +kernel
def cuts62449 : List PrefixCut := [⟨9,27428248,27428264⟩,
⟨64,193749347,193749461⟩]
theorem checked62449 : checkPrefixCuts (2^48) 8189247489 10 Manual.Count131072.C062449.packed 64 cuts62449 = true := by
 decide +kernel
def pointBounds62449 : List (Nat × Nat × Nat) := [(8189265920,114410349023228,114410737713097)]
theorem point_links_checked62449 : (cuts62449.take 1).map (fun c => (8189247489-1+2*2^10*c.k,114410321594980+c.lower,114410710284833+c.upper)) = pointBounds62449 := by
 decide +kernel
def cuts62450 : List PrefixCut := [⟨64,197492607,197492724⟩]
theorem checked62450 : checkPrefixCuts (2^48) 8189378561 10 Manual.Count131072.C062450.packed 64 cuts62450 = true := by
 decide +kernel
def cuts62451 : List PrefixCut := [⟨6,18697362,18697373⟩,
⟨64,196664581,196664693⟩]
theorem checked62451 : checkPrefixCuts (2^48) 8189509633 10 Manual.Count131072.C062451.packed 64 cuts62451 = true := by
 decide +kernel
def pointBounds62451 : List (Nat × Nat × Nat) := [(8189521920,114410731534296,114411120224391)]
theorem point_links_checked62451 : (cuts62451.take 1).map (fun c => (8189509633-1+2*2^10*c.k,114410712836934+c.lower,114411101527018+c.upper)) = pointBounds62451 := by
 decide +kernel
def cuts62452 : List PrefixCut := [⟨64,195458499,195458613⟩]
theorem checked62452 : checkPrefixCuts (2^48) 8189640705 10 Manual.Count131072.C062452.packed 64 cuts62452 = true := by
 decide +kernel
def cuts62453 : List PrefixCut := [⟨3,9210910,9210915⟩,
⟨64,198067394,198067506⟩]
theorem checked62453 : checkPrefixCuts (2^48) 8189771777 10 Manual.Count131072.C062453.packed 64 cuts62453 = true := by
 decide +kernel
def pointBounds62453 : List (Nat × Nat × Nat) := [(8189777920,114411114170924,114411502861239)]
theorem point_links_checked62453 : (cuts62453.take 1).map (fun c => (8189771777-1+2*2^10*c.k,114411104960014+c.lower,114411493650324+c.upper)) = pointBounds62453 := by
 decide +kernel
def cuts62454 : List PrefixCut := [⟨64,195864669,195864782⟩]
theorem checked62454 : checkPrefixCuts (2^48) 8189902849 10 Manual.Count131072.C062454.packed 64 cuts62454 = true := by
 decide +kernel
def pointBounds62454 : List (Nat × Nat × Nat) := [(8190033920,114411498892077,114411887582612)]
theorem point_links_checked62454 : (cuts62454.take 1).map (fun c => (8189902849-1+2*2^10*c.k,114411303027408+c.lower,114411691717830+c.upper)) = pointBounds62454 := by
 decide +kernel
def cuts62455 : List PrefixCut := [⟨64,194143144,194143258⟩]
theorem checked62455 : checkPrefixCuts (2^48) 8190033921 10 Manual.Count131072.C062455.packed 64 cuts62455 = true := by
 decide +kernel
def cuts62456 : List PrefixCut := [⟨61,188332059,188332164⟩,
⟨64,197473651,197473762⟩]
theorem checked62456 : checkPrefixCuts (2^48) 8190164993 10 Manual.Count131072.C062456.packed 64 cuts62456 = true := by
 decide +kernel
def pointBounds62456 : List (Nat × Nat × Nat) := [(8190289920,114411881367280,114412270058034)]
theorem point_links_checked62456 : (cuts62456.take 1).map (fun c => (8190164993-1+2*2^10*c.k,114411693035221+c.lower,114412081725870+c.upper)) = pointBounds62456 := by
 decide +kernel
def cuts62457 : List PrefixCut := [⟨64,198020334,198020452⟩]
theorem checked62457 : checkPrefixCuts (2^48) 8190296065 10 Manual.Count131072.C062457.packed 64 cuts62457 = true := by
 decide +kernel
def cuts62458 : List PrefixCut := [⟨58,179872043,179872149⟩,
⟨64,199563648,199563764⟩]
theorem checked62458 : checkPrefixCuts (2^48) 8190427137 10 Manual.Count131072.C062458.packed 64 cuts62458 = true := by
 decide +kernel
def pointBounds62458 : List (Nat × Nat × Nat) := [(8190545920,114412268401249,114412657092233)]
theorem point_links_checked62458 : (cuts62458.take 1).map (fun c => (8190427137-1+2*2^10*c.k,114412088529206+c.lower,114412477220084+c.upper)) = pointBounds62458 := by
 decide +kernel
def cuts62459 : List PrefixCut := [⟨64,196983046,196983161⟩]
theorem checked62459 : checkPrefixCuts (2^48) 8190558209 10 Manual.Count131072.C062459.packed 64 cuts62459 = true := by
 decide +kernel
def cuts62460 : List PrefixCut := [⟨55,170794008,170794102⟩,
⟨64,198045228,198045339⟩]
theorem checked62460 : checkPrefixCuts (2^48) 8190689281 10 Manual.Count131072.C062460.packed 64 cuts62460 = true := by
 decide +kernel
def pointBounds62460 : List (Nat × Nat × Nat) := [(8190801920,114412655869908,114413044561111)]
theorem point_links_checked62460 : (cuts62460.take 1).map (fun c => (8190689281-1+2*2^10*c.k,114412485075900+c.lower,114412873767009+c.upper)) = pointBounds62460 := by
 decide +kernel
def cuts62461 : List PrefixCut := [⟨64,200035171,200035292⟩]
theorem checked62461 : checkPrefixCuts (2^48) 8190820353 10 Manual.Count131072.C062461.packed 64 cuts62461 = true := by
 decide +kernel
def cuts62462 : List PrefixCut := [⟨52,159482887,159482975⟩,
⟨64,196286334,196286443⟩]
theorem checked62462 : checkPrefixCuts (2^48) 8190951425 10 Manual.Count131072.C062462.packed 64 cuts62462 = true := by
 decide +kernel
def pointBounds62462 : List (Nat × Nat × Nat) := [(8191057920,114413042639186,114413431330615)]
theorem point_links_checked62462 : (cuts62462.take 1).map (fun c => (8190951425-1+2*2^10*c.k,114412883156299+c.lower,114413271847640+c.upper)) = pointBounds62462 := by
 decide +kernel
def cuts62463 : List PrefixCut := [⟨64,197107904,197108014⟩]
theorem checked62463 : checkPrefixCuts (2^48) 8191082497 10 Manual.Count131072.C062463.packed 64 cuts62463 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000076
