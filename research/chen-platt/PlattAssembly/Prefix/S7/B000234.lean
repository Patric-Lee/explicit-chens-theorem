import PlattAssemblyKernel
import PlattCertificates.Count131072.C067488
import PlattCertificates.Count131072.C067489
import PlattCertificates.Count131072.C067490
import PlattCertificates.Count131072.C067491
import PlattCertificates.Count131072.C067492
import PlattCertificates.Count131072.C067493
import PlattCertificates.Count131072.C067494
import PlattCertificates.Count131072.C067495
import PlattCertificates.Count131072.C067496
import PlattCertificates.Count131072.C067497
import PlattCertificates.Count131072.C067498
import PlattCertificates.Count131072.C067499
import PlattCertificates.Count131072.C067500
import PlattCertificates.Count131072.C067501
import PlattCertificates.Count131072.C067502
import PlattCertificates.Count131072.C067503
import PlattCertificates.Count131072.C067504
import PlattCertificates.Count131072.C067505
import PlattCertificates.Count131072.C067506
import PlattCertificates.Count131072.C067507
import PlattCertificates.Count131072.C067508
import PlattCertificates.Count131072.C067509
import PlattCertificates.Count131072.C067510
import PlattCertificates.Count131072.C067511
import PlattCertificates.Count131072.C067512
import PlattCertificates.Count131072.C067513
import PlattCertificates.Count131072.C067514
import PlattCertificates.Count131072.C067515
import PlattCertificates.Count131072.C067516
import PlattCertificates.Count131072.C067517
import PlattCertificates.Count131072.C067518
import PlattCertificates.Count131072.C067519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000234
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67488 : List PrefixCut := [⟨64,182056655,182056757⟩]
theorem checked67488 : checkPrefixCuts (2^48) 8849719297 10 Manual.Count131072.C067488.packed 64 cuts67488 = true := by
 decide +kernel
def cuts67489 : List PrefixCut := [⟨5,14980434,14980442⟩,
⟨64,182976325,182976429⟩]
theorem checked67489 : checkPrefixCuts (2^48) 8849850369 10 Manual.Count131072.C067489.packed 64 cuts67489 = true := by
 decide +kernel
def pointBounds67489 : List (Nat × Nat × Nat) := [(8849860608,115365394995996,115365784238374)]
theorem point_links_checked67489 : (cuts67489.take 1).map (fun c => (8849850369-1+2*2^10*c.k,115365380015562+c.lower,115365769257932+c.upper)) = pointBounds67489 := by
 decide +kernel
def cuts67490 : List PrefixCut := [⟨64,184341229,184341335⟩]
theorem checked67490 : checkPrefixCuts (2^48) 8849981441 10 Manual.Count131072.C067490.packed 64 cuts67490 = true := by
 decide +kernel
def cuts67491 : List PrefixCut := [⟨13,37783890,37783912⟩,
⟨64,181635124,181635227⟩]
theorem checked67491 : checkPrefixCuts (2^48) 8850112513 10 Manual.Count131072.C067491.packed 64 cuts67491 = true := by
 decide +kernel
def pointBounds67491 : List (Nat × Nat × Nat) := [(8850139136,115365785117006,115366174359608)]
theorem point_links_checked67491 : (cuts67491.take 1).map (fun c => (8850112513-1+2*2^10*c.k,115365747333116+c.lower,115366136575696+c.upper)) = pointBounds67491 := by
 decide +kernel
def cuts67492 : List PrefixCut := [⟨64,180169445,180169548⟩]
theorem checked67492 : checkPrefixCuts (2^48) 8850243585 10 Manual.Count131072.C067492.packed 64 cuts67492 = true := by
 decide +kernel
def cuts67493 : List PrefixCut := [⟨21,58168873,58168908⟩,
⟨64,182647439,182647546⟩]
theorem checked67493 : checkPrefixCuts (2^48) 8850374657 10 Manual.Count131072.C067493.packed 64 cuts67493 = true := by
 decide +kernel
def pointBounds67493 : List (Nat × Nat × Nat) := [(8850417664,115366167306558,115366556549379)]
theorem point_links_checked67493 : (cuts67493.take 1).map (fun c => (8850374657-1+2*2^10*c.k,115366109137685+c.lower,115366498380471+c.upper)) = pointBounds67493 := by
 decide +kernel
def cuts67494 : List PrefixCut := [⟨64,180513935,180514037⟩]
theorem checked67494 : checkPrefixCuts (2^48) 8850505729 10 Manual.Count131072.C067494.packed 64 cuts67494 = true := by
 decide +kernel
def cuts67495 : List PrefixCut := [⟨29,82591554,82591601⟩,
⟨64,180034238,180034344⟩]
theorem checked67495 : checkPrefixCuts (2^48) 8850636801 10 Manual.Count131072.C067495.packed 64 cuts67495 = true := by
 decide +kernel
def pointBounds67495 : List (Nat × Nat × Nat) := [(8850696192,115366554890613,115366944133655)]
theorem point_links_checked67495 : (cuts67495.take 1).map (fun c => (8850636801-1+2*2^10*c.k,115366472299059+c.lower,115366861542054+c.upper)) = pointBounds67495 := by
 decide +kernel
def cuts67496 : List PrefixCut := [⟨64,181494459,181494567⟩]
theorem checked67496 : checkPrefixCuts (2^48) 8850767873 10 Manual.Count131072.C067496.packed 64 cuts67496 = true := by
 decide +kernel
def cuts67497 : List PrefixCut := [⟨37,103387347,103387412⟩,
⟨64,180633116,180633229⟩]
theorem checked67497 : checkPrefixCuts (2^48) 8850898945 10 Manual.Count131072.C067497.packed 64 cuts67497 = true := by
 decide +kernel
def pointBounds67497 : List (Nat × Nat × Nat) := [(8850974720,115366937215103,115367326458377)]
theorem point_links_checked67497 : (cuts67497.take 1).map (fun c => (8850898945-1+2*2^10*c.k,115366833827756+c.lower,115367223070965+c.upper)) = pointBounds67497 := by
 decide +kernel
def cuts67498 : List PrefixCut := [⟨64,181520893,181520992⟩]
theorem checked67498 : checkPrefixCuts (2^48) 8851030017 10 Manual.Count131072.C067498.packed 64 cuts67498 = true := by
 decide +kernel
def cuts67499 : List PrefixCut := [⟨45,129747002,129747076⟩,
⟨64,184412060,184412167⟩]
theorem checked67499 : checkPrefixCuts (2^48) 8851161089 10 Manual.Count131072.C067499.packed 64 cuts67499 = true := by
 decide +kernel
def pointBounds67499 : List (Nat × Nat × Nat) := [(8851253248,115367325728767,115367714972262)]
theorem point_links_checked67499 : (cuts67499.take 1).map (fun c => (8851161089-1+2*2^10*c.k,115367195981765+c.lower,115367585225186+c.upper)) = pointBounds67499 := by
 decide +kernel
def cuts67500 : List PrefixCut := [⟨64,183741524,183741639⟩]
theorem checked67500 : checkPrefixCuts (2^48) 8851292161 10 Manual.Count131072.C067500.packed 64 cuts67500 = true := by
 decide +kernel
def cuts67501 : List PrefixCut := [⟨53,152956872,152956957⟩,
⟨64,182943826,182943929⟩]
theorem checked67501 : checkPrefixCuts (2^48) 8851423233 10 Manual.Count131072.C067501.packed 64 cuts67501 = true := by
 decide +kernel
def pointBounds67501 : List (Nat × Nat × Nat) := [(8851531776,115367717092221,115368106335949)]
theorem point_links_checked67501 : (cuts67501.take 1).map (fun c => (8851423233-1+2*2^10*c.k,115367564135349+c.lower,115367953378992+c.upper)) = pointBounds67501 := by
 decide +kernel
def cuts67502 : List PrefixCut := [⟨64,182623112,182623219⟩]
theorem checked67502 : checkPrefixCuts (2^48) 8851554305 10 Manual.Count131072.C067502.packed 64 cuts67502 = true := by
 decide +kernel
def cuts67503 : List PrefixCut := [⟨61,172699250,172699353⟩,
⟨64,181412055,181412163⟩]
theorem checked67503 : checkPrefixCuts (2^48) 8851685377 10 Manual.Count131072.C067503.packed 64 cuts67503 = true := by
 decide +kernel
def pointBounds67503 : List (Nat × Nat × Nat) := [(8851810304,115368102401537,115368491645493)]
theorem point_links_checked67503 : (cuts67503.take 1).map (fun c => (8851685377-1+2*2^10*c.k,115367929702287+c.lower,115368318946140+c.upper)) = pointBounds67503 := by
 decide +kernel
def cuts67504 : List PrefixCut := [⟨64,185129759,185129867⟩]
theorem checked67504 : checkPrefixCuts (2^48) 8851816449 10 Manual.Count131072.C067504.packed 64 cuts67504 = true := by
 decide +kernel
def cuts67505 : List PrefixCut := [⟨64,181851842,181851944⟩]
theorem checked67505 : checkPrefixCuts (2^48) 8851947521 10 Manual.Count131072.C067505.packed 64 cuts67505 = true := by
 decide +kernel
def cuts67506 : List PrefixCut := [⟨5,13736556,13736565⟩,
⟨64,183057442,183057543⟩]
theorem checked67506 : checkPrefixCuts (2^48) 8852078593 10 Manual.Count131072.C067506.packed 64 cuts67506 = true := by
 decide +kernel
def pointBounds67506 : List (Nat × Nat × Nat) := [(8852088832,115368491832499,115368881076679)]
theorem point_links_checked67506 : (cuts67506.take 1).map (fun c => (8852078593-1+2*2^10*c.k,115368478095943+c.lower,115368867340114+c.upper)) = pointBounds67506 := by
 decide +kernel
def cuts67507 : List PrefixCut := [⟨64,183976861,183976965⟩]
theorem checked67507 : checkPrefixCuts (2^48) 8852209665 10 Manual.Count131072.C067507.packed 64 cuts67507 = true := by
 decide +kernel
def cuts67508 : List PrefixCut := [⟨13,37106650,37106670⟩,
⟨64,182320711,182320818⟩]
theorem checked67508 : checkPrefixCuts (2^48) 8852340737 10 Manual.Count131072.C067508.packed 64 cuts67508 = true := by
 decide +kernel
def pointBounds67508 : List (Nat × Nat × Nat) := [(8852367360,115368882236896,115369271481292)]
theorem point_links_checked67508 : (cuts67508.take 1).map (fun c => (8852340737-1+2*2^10*c.k,115368845130246+c.lower,115369234374622+c.upper)) = pointBounds67508 := by
 decide +kernel
def cuts67509 : List PrefixCut := [⟨64,181809276,181809382⟩]
theorem checked67509 : checkPrefixCuts (2^48) 8852471809 10 Manual.Count131072.C067509.packed 64 cuts67509 = true := by
 decide +kernel
def cuts67510 : List PrefixCut := [⟨21,59934789,59934826⟩,
⟨64,182951226,182951333⟩]
theorem checked67510 : checkPrefixCuts (2^48) 8852602881 10 Manual.Count131072.C067510.packed 64 cuts67510 = true := by
 decide +kernel
def pointBounds67510 : List (Nat × Nat × Nat) := [(8852645888,115369269195022,115369658439648)]
theorem point_links_checked67510 : (cuts67510.take 1).map (fun c => (8852602881-1+2*2^10*c.k,115369209260233+c.lower,115369598504822+c.upper)) = pointBounds67510 := by
 decide +kernel
def cuts67511 : List PrefixCut := [⟨64,181040816,181040924⟩]
theorem checked67511 : checkPrefixCuts (2^48) 8852733953 10 Manual.Count131072.C067511.packed 64 cuts67511 = true := by
 decide +kernel
def cuts67512 : List PrefixCut := [⟨29,82221021,82221073⟩,
⟨64,179957119,179957232⟩]
theorem checked67512 : checkPrefixCuts (2^48) 8852865025 10 Manual.Count131072.C067512.packed 64 cuts67512 = true := by
 decide +kernel
def pointBounds67512 : List (Nat × Nat × Nat) := [(8852924416,115369655473296,115370044718152)]
theorem point_links_checked67512 : (cuts67512.take 1).map (fun c => (8852865025-1+2*2^10*c.k,115369573252275+c.lower,115369962497079+c.upper)) = pointBounds67512 := by
 decide +kernel
def cuts67513 : List PrefixCut := [⟨64,181671334,181671444⟩]
theorem checked67513 : checkPrefixCuts (2^48) 8852996097 10 Manual.Count131072.C067513.packed 64 cuts67513 = true := by
 decide +kernel
def cuts67514 : List PrefixCut := [⟨37,104569491,104569548⟩,
⟨64,183671635,183671736⟩]
theorem checked67514 : checkPrefixCuts (2^48) 8853127169 10 Manual.Count131072.C067514.packed 64 cuts67514 = true := by
 decide +kernel
def pointBounds67514 : List (Nat × Nat × Nat) := [(8853202944,115370039450219,115370428695303)]
theorem point_links_checked67514 : (cuts67514.take 1).map (fun c => (8853127169-1+2*2^10*c.k,115369934880728+c.lower,115370324125755+c.upper)) = pointBounds67514 := by
 decide +kernel
def cuts67515 : List PrefixCut := [⟨64,182047471,182047576⟩]
theorem checked67515 : checkPrefixCuts (2^48) 8853258241 10 Manual.Count131072.C067515.packed 64 cuts67515 = true := by
 decide +kernel
def cuts67516 : List PrefixCut := [⟨45,126662240,126662313⟩,
⟨64,180041845,180041948⟩]
theorem checked67516 : checkPrefixCuts (2^48) 8853389313 10 Manual.Count131072.C067516.packed 64 cuts67516 = true := by
 decide +kernel
def pointBounds67516 : List (Nat × Nat × Nat) := [(8853481472,115370427262074,115370816507380)]
theorem point_links_checked67516 : (cuts67516.take 1).map (fun c => (8853389313-1+2*2^10*c.k,115370300599834+c.lower,115370689845067+c.upper)) = pointBounds67516 := by
 decide +kernel
def cuts67517 : List PrefixCut := [⟨64,181279058,181279166⟩]
theorem checked67517 : checkPrefixCuts (2^48) 8853520385 10 Manual.Count131072.C067517.packed 64 cuts67517 = true := by
 decide +kernel
def cuts67518 : List PrefixCut := [⟨53,151169825,151169910⟩,
⟨64,183183892,183183995⟩]
theorem checked67518 : checkPrefixCuts (2^48) 8853651457 10 Manual.Count131072.C067518.packed 64 cuts67518 = true := by
 decide +kernel
def pointBounds67518 : List (Nat × Nat × Nat) := [(8853760000,115370813090562,115371202336091)]
theorem point_links_checked67518 : (cuts67518.take 1).map (fun c => (8853651457-1+2*2^10*c.k,115370661920737+c.lower,115371051166181+c.upper)) = pointBounds67518 := by
 decide +kernel
def cuts67519 : List PrefixCut := [⟨64,181210135,181210240⟩]
theorem checked67519 : checkPrefixCuts (2^48) 8853782529 10 Manual.Count131072.C067519.packed 64 cuts67519 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000234
