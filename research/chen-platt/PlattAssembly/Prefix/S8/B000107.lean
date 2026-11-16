import PlattAssemblyKernel
import PlattCertificates.Count131072.C073424
import PlattCertificates.Count131072.C073425
import PlattCertificates.Count131072.C073426
import PlattCertificates.Count131072.C073427
import PlattCertificates.Count131072.C073428
import PlattCertificates.Count131072.C073429
import PlattCertificates.Count131072.C073430
import PlattCertificates.Count131072.C073431
import PlattCertificates.Count131072.C073432
import PlattCertificates.Count131072.C073433
import PlattCertificates.Count131072.C073434
import PlattCertificates.Count131072.C073435
import PlattCertificates.Count131072.C073436
import PlattCertificates.Count131072.C073437
import PlattCertificates.Count131072.C073438
import PlattCertificates.Count131072.C073439
import PlattCertificates.Count131072.C073440
import PlattCertificates.Count131072.C073441
import PlattCertificates.Count131072.C073442
import PlattCertificates.Count131072.C073443
import PlattCertificates.Count131072.C073444
import PlattCertificates.Count131072.C073445
import PlattCertificates.Count131072.C073446
import PlattCertificates.Count131072.C073447
import PlattCertificates.Count131072.C073448
import PlattCertificates.Count131072.C073449
import PlattCertificates.Count131072.C073450
import PlattCertificates.Count131072.C073451
import PlattCertificates.Count131072.C073452
import PlattCertificates.Count131072.C073453
import PlattCertificates.Count131072.C073454
import PlattCertificates.Count131072.C073455
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73424 : List PrefixCut := [⟨64,165093180,165093273⟩]
theorem checked73424 : checkPrefixCuts (2^48) 9627762689 10 Manual.Count131072.C073424.packed 64 cuts73424 = true := by
 decide +kernel
def cuts73425 : List PrefixCut := [⟨18,47010360,47010389⟩,
⟨64,167225083,167225185⟩]
theorem checked73425 : checkPrefixCuts (2^48) 9627893761 10 Manual.Count131072.C073425.packed 64 cuts73425 = true := by
 decide +kernel
def pointBounds73425 : List (Nat × Nat × Nat) := [(9627930624,116399089536945,116399479389098)]
theorem point_links_checked73425 : (cuts73425.take 1).map (fun c => (9627893761-1+2*2^10*c.k,116399042526585+c.lower,116399432378709+c.upper)) = pointBounds73425 := by
 decide +kernel
def cuts73426 : List PrefixCut := [⟨64,165761082,165761180⟩]
theorem checked73426 : checkPrefixCuts (2^48) 9628024833 10 Manual.Count131072.C073426.packed 64 cuts73426 = true := by
 decide +kernel
def cuts73427 : List PrefixCut := [⟨37,99952565,99952623⟩,
⟨64,170056284,170056387⟩]
theorem checked73427 : checkPrefixCuts (2^48) 9628155905 10 Manual.Count131072.C073427.packed 64 cuts73427 = true := by
 decide +kernel
def pointBounds73427 : List (Nat × Nat × Nat) := [(9628231680,116399475465315,116399865317697)]
theorem point_links_checked73427 : (cuts73427.take 1).map (fun c => (9628155905-1+2*2^10*c.k,116399375512750+c.lower,116399765365074+c.upper)) = pointBounds73427 := by
 decide +kernel
def cuts73428 : List PrefixCut := [⟨64,165931963,165932068⟩]
theorem checked73428 : checkPrefixCuts (2^48) 9628286977 10 Manual.Count131072.C073428.packed 64 cuts73428 = true := by
 decide +kernel
def cuts73429 : List PrefixCut := [⟨56,146401811,146401900⟩,
⟨64,167274450,167274553⟩]
theorem checked73429 : checkPrefixCuts (2^48) 9628418049 10 Manual.Count131072.C073429.packed 64 cuts73429 = true := by
 decide +kernel
def pointBounds73429 : List (Nat × Nat × Nat) := [(9628532736,116399857902808,116400247755429)]
theorem point_links_checked73429 : (cuts73429.take 1).map (fun c => (9628418049-1+2*2^10*c.k,116399711500997+c.lower,116400101353529+c.upper)) = pointBounds73429 := by
 decide +kernel
def cuts73430 : List PrefixCut := [⟨64,168353804,168353899⟩]
theorem checked73430 : checkPrefixCuts (2^48) 9628549121 10 Manual.Count131072.C073430.packed 64 cuts73430 = true := by
 decide +kernel
def cuts73431 : List PrefixCut := [⟨64,168293042,168293144⟩]
theorem checked73431 : checkPrefixCuts (2^48) 9628680193 10 Manual.Count131072.C073431.packed 64 cuts73431 = true := by
 decide +kernel
def cuts73432 : List PrefixCut := [⟨11,27683210,27683227⟩,
⟨64,164899797,164899893⟩]
theorem checked73432 : checkPrefixCuts (2^48) 9628811265 10 Manual.Count131072.C073432.packed 64 cuts73432 = true := by
 decide +kernel
def pointBounds73432 : List (Nat × Nat × Nat) := [(9628833792,116400243105503,116400632958352)]
theorem point_links_checked73432 : (cuts73432.take 1).map (fun c => (9628811265-1+2*2^10*c.k,116400215422293+c.lower,116400605275125+c.upper)) = pointBounds73432 := by
 decide +kernel
def cuts73433 : List PrefixCut := [⟨64,167645362,167645463⟩]
theorem checked73433 : checkPrefixCuts (2^48) 9628942337 10 Manual.Count131072.C073433.packed 64 cuts73433 = true := by
 decide +kernel
def cuts73434 : List PrefixCut := [⟨30,77697809,77697853⟩,
⟨64,165158402,165158497⟩]
theorem checked73434 : checkPrefixCuts (2^48) 9629073409 10 Manual.Count131072.C073434.packed 64 cuts73434 = true := by
 decide +kernel
def pointBounds73434 : List (Nat × Nat × Nat) := [(9629134848,116400625665261,116401015518334)]
theorem point_links_checked73434 : (cuts73434.take 1).map (fun c => (9629073409-1+2*2^10*c.k,116400547967452+c.lower,116400937820481+c.upper)) = pointBounds73434 := by
 decide +kernel
def cuts73435 : List PrefixCut := [⟨64,167728481,167728579⟩]
theorem checked73435 : checkPrefixCuts (2^48) 9629204481 10 Manual.Count131072.C073435.packed 64 cuts73435 = true := by
 decide +kernel
def cuts73436 : List PrefixCut := [⟨49,129346403,129346479⟩,
⟨64,168690825,168690924⟩]
theorem checked73436 : checkPrefixCuts (2^48) 9629335553 10 Manual.Count131072.C073436.packed 64 cuts73436 = true := by
 decide +kernel
def pointBounds73436 : List (Nat × Nat × Nat) := [(9629435904,116401010200738,116401400054036)]
theorem point_links_checked73436 : (cuts73436.take 1).map (fun c => (9629335553-1+2*2^10*c.k,116400880854335+c.lower,116401270707557+c.upper)) = pointBounds73436 := by
 decide +kernel
def cuts73437 : List PrefixCut := [⟨64,167870081,167870183⟩]
theorem checked73437 : checkPrefixCuts (2^48) 9629466625 10 Manual.Count131072.C073437.packed 64 cuts73437 = true := by
 decide +kernel
def cuts73438 : List PrefixCut := [⟨64,167049361,167049458⟩]
theorem checked73438 : checkPrefixCuts (2^48) 9629597697 10 Manual.Count131072.C073438.packed 64 cuts73438 = true := by
 decide +kernel
def cuts73439 : List PrefixCut := [⟨4,11195003,11195009⟩,
⟨64,164591806,164591902⟩]
theorem checked73439 : checkPrefixCuts (2^48) 9629728769 10 Manual.Count131072.C073439.packed 64 cuts73439 = true := by
 decide +kernel
def pointBounds73439 : List (Nat × Nat × Nat) := [(9629736960,116401395659605,116401785513131)]
theorem point_links_checked73439 : (cuts73439.take 1).map (fun c => (9629728769-1+2*2^10*c.k,116401384464602+c.lower,116401774318122+c.upper)) = pointBounds73439 := by
 decide +kernel
def cuts73440 : List PrefixCut := [⟨64,165963327,165963424⟩]
theorem checked73440 : checkPrefixCuts (2^48) 9629859841 10 Manual.Count131072.C073440.packed 64 cuts73440 = true := by
 decide +kernel
def cuts73441 : List PrefixCut := [⟨23,60708461,60708498⟩,
⟨64,166662567,166662669⟩]
theorem checked73441 : checkPrefixCuts (2^48) 9629990913 10 Manual.Count131072.C073441.packed 64 cuts73441 = true := by
 decide +kernel
def pointBounds73441 : List (Nat × Nat × Nat) := [(9630038016,116401775728196,116402165581946)]
theorem point_links_checked73441 : (cuts73441.take 1).map (fun c => (9629990913-1+2*2^10*c.k,116401715019735+c.lower,116402104873448+c.upper)) = pointBounds73441 := by
 decide +kernel
def cuts73442 : List PrefixCut := [⟨64,165286557,165286658⟩]
theorem checked73442 : checkPrefixCuts (2^48) 9630121985 10 Manual.Count131072.C073442.packed 64 cuts73442 = true := by
 decide +kernel
def cuts73443 : List PrefixCut := [⟨42,108523795,108523861⟩,
⟨64,165722721,165722825⟩]
theorem checked73443 : checkPrefixCuts (2^48) 9630253057 10 Manual.Count131072.C073443.packed 64 cuts73443 = true := by
 decide +kernel
def pointBounds73443 : List (Nat × Nat × Nat) := [(9630339072,116402155492654,116402545346636)]
theorem point_links_checked73443 : (cuts73443.take 1).map (fun c => (9630253057-1+2*2^10*c.k,116402046968859+c.lower,116402436822775+c.upper)) = pointBounds73443 := by
 decide +kernel
def cuts73444 : List PrefixCut := [⟨64,166714218,166714312⟩]
theorem checked73444 : checkPrefixCuts (2^48) 9630384129 10 Manual.Count131072.C073444.packed 64 cuts73444 = true := by
 decide +kernel
def cuts73445 : List PrefixCut := [⟨61,159609772,159609875⟩,
⟨64,167384156,167384264⟩]
theorem checked73445 : checkPrefixCuts (2^48) 9630515201 10 Manual.Count131072.C073445.packed 64 cuts73445 = true := by
 decide +kernel
def pointBounds73445 : List (Nat × Nat × Nat) := [(9630640128,116402539015570,116402928869787)]
theorem point_links_checked73445 : (cuts73445.take 1).map (fun c => (9630515201-1+2*2^10*c.k,116402379405798+c.lower,116402769259912+c.upper)) = pointBounds73445 := by
 decide +kernel
def cuts73446 : List PrefixCut := [⟨64,164576104,164576202⟩]
theorem checked73446 : checkPrefixCuts (2^48) 9630646273 10 Manual.Count131072.C073446.packed 64 cuts73446 = true := by
 decide +kernel
def cuts73447 : List PrefixCut := [⟨64,166327455,166327556⟩]
theorem checked73447 : checkPrefixCuts (2^48) 9630777345 10 Manual.Count131072.C073447.packed 64 cuts73447 = true := by
 decide +kernel
def cuts73448 : List PrefixCut := [⟨16,39835246,39835273⟩,
⟨64,166208276,166208377⟩]
theorem checked73448 : checkPrefixCuts (2^48) 9630908417 10 Manual.Count131072.C073448.packed 64 cuts73448 = true := by
 decide +kernel
def pointBounds73448 : List (Nat × Nat × Nat) := [(9630941184,116402917528759,116403307383207)]
theorem point_links_checked73448 : (cuts73448.take 1).map (fun c => (9630908417-1+2*2^10*c.k,116402877693513+c.lower,116403267547934+c.upper)) = pointBounds73448 := by
 decide +kernel
def cuts73449 : List PrefixCut := [⟨64,165884559,165884655⟩]
theorem checked73449 : checkPrefixCuts (2^48) 9631039489 10 Manual.Count131072.C073449.packed 64 cuts73449 = true := by
 decide +kernel
def cuts73450 : List PrefixCut := [⟨35,92001246,92001300⟩,
⟨64,167402004,167402104⟩]
theorem checked73450 : checkPrefixCuts (2^48) 9631170561 10 Manual.Count131072.C073450.packed 64 cuts73450 = true := by
 decide +kernel
def pointBounds73450 : List (Nat × Nat × Nat) := [(9631242240,116403301787594,116403691642266)]
theorem point_links_checked73450 : (cuts73450.take 1).map (fun c => (9631170561-1+2*2^10*c.k,116403209786348+c.lower,116403599640966+c.upper)) = pointBounds73450 := by
 decide +kernel
def cuts73451 : List PrefixCut := [⟨64,168597932,168598030⟩]
theorem checked73451 : checkPrefixCuts (2^48) 9631301633 10 Manual.Count131072.C073451.packed 64 cuts73451 = true := by
 decide +kernel
def cuts73452 : List PrefixCut := [⟨54,141972355,141972437⟩,
⟨64,167514348,167514443⟩]
theorem checked73452 : checkPrefixCuts (2^48) 9631432705 10 Manual.Count131072.C073452.packed 64 cuts73452 = true := by
 decide +kernel
def pointBounds73452 : List (Nat × Nat × Nat) := [(9631543296,116403687758639,116404077613537)]
theorem point_links_checked73452 : (cuts73452.take 1).map (fun c => (9631432705-1+2*2^10*c.k,116403545786284+c.lower,116403935641100+c.upper)) = pointBounds73452 := by
 decide +kernel
def cuts73453 : List PrefixCut := [⟨64,167745849,167745951⟩]
theorem checked73453 : checkPrefixCuts (2^48) 9631563777 10 Manual.Count131072.C073453.packed 64 cuts73453 = true := by
 decide +kernel
def cuts73454 : List PrefixCut := [⟨64,167363660,167363764⟩]
theorem checked73454 : checkPrefixCuts (2^48) 9631694849 10 Manual.Count131072.C073454.packed 64 cuts73454 = true := by
 decide +kernel
def cuts73455 : List PrefixCut := [⟨9,23203374,23203386⟩,
⟨64,165081971,165082068⟩]
theorem checked73455 : checkPrefixCuts (2^48) 9631825921 10 Manual.Count131072.C073455.packed 64 cuts73455 = true := by
 decide +kernel
def pointBounds73455 : List (Nat × Nat × Nat) := [(9631844352,116404071613515,116404461468644)]
theorem point_links_checked73455 : (cuts73455.take 1).map (fun c => (9631825921-1+2*2^10*c.k,116404048410141+c.lower,116404438265258+c.upper)) = pointBounds73455 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000107
