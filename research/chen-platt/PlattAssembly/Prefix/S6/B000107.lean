import PlattAssemblyKernel
import PlattCertificates.Count131072.C053424
import PlattCertificates.Count131072.C053425
import PlattCertificates.Count131072.C053426
import PlattCertificates.Count131072.C053427
import PlattCertificates.Count131072.C053428
import PlattCertificates.Count131072.C053429
import PlattCertificates.Count131072.C053430
import PlattCertificates.Count131072.C053431
import PlattCertificates.Count131072.C053432
import PlattCertificates.Count131072.C053433
import PlattCertificates.Count131072.C053434
import PlattCertificates.Count131072.C053435
import PlattCertificates.Count131072.C053436
import PlattCertificates.Count131072.C053437
import PlattCertificates.Count131072.C053438
import PlattCertificates.Count131072.C053439
import PlattCertificates.Count131072.C053440
import PlattCertificates.Count131072.C053441
import PlattCertificates.Count131072.C053442
import PlattCertificates.Count131072.C053443
import PlattCertificates.Count131072.C053444
import PlattCertificates.Count131072.C053445
import PlattCertificates.Count131072.C053446
import PlattCertificates.Count131072.C053447
import PlattCertificates.Count131072.C053448
import PlattCertificates.Count131072.C053449
import PlattCertificates.Count131072.C053450
import PlattCertificates.Count131072.C053451
import PlattCertificates.Count131072.C053452
import PlattCertificates.Count131072.C053453
import PlattCertificates.Count131072.C053454
import PlattCertificates.Count131072.C053455
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53424 : List PrefixCut := [⟨64,232969231,232969362⟩]
theorem checked53424 : checkPrefixCuts (2^48) 7006322689 10 Manual.Count131072.C053424.packed 64 cuts53424 = true := by
 decide +kernel
def cuts53425 : List PrefixCut := [⟨40,145709029,145709109⟩,
⟨64,234089738,234089868⟩]
theorem checked53425 : checkPrefixCuts (2^48) 7006453761 10 Manual.Count131072.C053425.packed 64 cuts53425 = true := by
 decide +kernel
def pointBounds53425 : List (Nat × Nat × Nat) := [(7006535680,112480341971351,112480729561431)]
theorem point_links_checked53425 : (cuts53425.take 1).map (fun c => (7006453761-1+2*2^10*c.k,112480196262322+c.lower,112480583852322+c.upper)) = pointBounds53425 := by
 decide +kernel
def cuts53426 : List PrefixCut := [⟨64,231514312,231514445⟩]
theorem checked53426 : checkPrefixCuts (2^48) 7006584833 10 Manual.Count131072.C053426.packed 64 cuts53426 = true := by
 decide +kernel
def cuts53427 : List PrefixCut := [⟨19,70863491,70863531⟩,
⟨64,234322023,234322156⟩]
theorem checked53427 : checkPrefixCuts (2^48) 7006715905 10 Manual.Count131072.C053427.packed 64 cuts53427 = true := by
 decide +kernel
def pointBounds53427 : List (Nat × Nat × Nat) := [(7006754816,112480732729863,112481120320166)]
theorem point_links_checked53427 : (cuts53427.take 1).map (fun c => (7006715905-1+2*2^10*c.k,112480661866372+c.lower,112481049456635+c.upper)) = pointBounds53427 := by
 decide +kernel
def cuts53428 : List PrefixCut := [⟨62,220338170,220338296⟩,
⟨64,227970597,227970727⟩]
theorem checked53428 : checkPrefixCuts (2^48) 7006846977 10 Manual.Count131072.C053428.packed 64 cuts53428 = true := by
 decide +kernel
def pointBounds53428 : List (Nat × Nat × Nat) := [(7006973952,112481116526565,112481504117087)]
theorem point_links_checked53428 : (cuts53428.take 1).map (fun c => (7006846977-1+2*2^10*c.k,112480896188395+c.lower,112481283778791+c.upper)) = pointBounds53428 := by
 decide +kernel
def cuts53429 : List PrefixCut := [⟨64,235518354,235518484⟩]
theorem checked53429 : checkPrefixCuts (2^48) 7006978049 10 Manual.Count131072.C053429.packed 64 cuts53429 = true := by
 decide +kernel
def cuts53430 : List PrefixCut := [⟨41,148266232,148266314⟩,
⟨64,232541400,232541529⟩]
theorem checked53430 : checkPrefixCuts (2^48) 7007109121 10 Manual.Count131072.C053430.packed 64 cuts53430 = true := by
 decide +kernel
def pointBounds53430 : List (Nat × Nat × Nat) := [(7007193088,112481507943578,112481895534316)]
theorem point_links_checked53430 : (cuts53430.take 1).map (fun c => (7007109121-1+2*2^10*c.k,112481359677346+c.lower,112481747268002+c.upper)) = pointBounds53430 := by
 decide +kernel
def cuts53431 : List PrefixCut := [⟨64,237116293,237116428⟩]
theorem checked53431 : checkPrefixCuts (2^48) 7007240193 10 Manual.Count131072.C053431.packed 64 cuts53431 = true := by
 decide +kernel
def cuts53432 : List PrefixCut := [⟨20,73789139,73789181⟩,
⟨64,233095065,233095195⟩]
theorem checked53432 : checkPrefixCuts (2^48) 7007371265 10 Manual.Count131072.C053432.packed 64 cuts53432 = true := by
 decide +kernel
def pointBounds53432 : List (Nat × Nat × Nat) := [(7007412224,112481903124178,112482290715140)]
theorem point_links_checked53432 : (cuts53432.take 1).map (fun c => (7007371265-1+2*2^10*c.k,112481829335039+c.lower,112482216925959+c.upper)) = pointBounds53432 := by
 decide +kernel
def cuts53433 : List PrefixCut := [⟨63,228913309,228913442⟩,
⟨64,232287329,232287464⟩]
theorem checked53433 : checkPrefixCuts (2^48) 7007502337 10 Manual.Count131072.C053433.packed 64 cuts53433 = true := by
 decide +kernel
def pointBounds53433 : List (Nat × Nat × Nat) := [(7007631360,112482291343413,112482678934596)]
theorem point_links_checked53433 : (cuts53433.take 1).map (fun c => (7007502337-1+2*2^10*c.k,112482062430104+c.lower,112482450021154+c.upper)) = pointBounds53433 := by
 decide +kernel
def cuts53434 : List PrefixCut := [⟨64,230716509,230716640⟩]
theorem checked53434 : checkPrefixCuts (2^48) 7007633409 10 Manual.Count131072.C053434.packed 64 cuts53434 = true := by
 decide +kernel
def cuts53435 : List PrefixCut := [⟨42,154277234,154277321⟩,
⟨64,236857557,236857689⟩]
theorem checked53435 : checkPrefixCuts (2^48) 7007764481 10 Manual.Count131072.C053435.packed 64 cuts53435 = true := by
 decide +kernel
def pointBounds53435 : List (Nat × Nat × Nat) := [(7007850496,112482679711176,112483067302579)]
theorem point_links_checked53435 : (cuts53435.take 1).map (fun c => (7007764481-1+2*2^10*c.k,112482525433942+c.lower,112482913025258+c.upper)) = pointBounds53435 := by
 decide +kernel
def cuts53436 : List PrefixCut := [⟨64,232234151,232234282⟩]
theorem checked53436 : checkPrefixCuts (2^48) 7007895553 10 Manual.Count131072.C053436.packed 64 cuts53436 = true := by
 decide +kernel
def cuts53437 : List PrefixCut := [⟨21,73902721,73902763⟩,
⟨64,228815828,228815955⟩]
theorem checked53437 : checkPrefixCuts (2^48) 7008026625 10 Manual.Count131072.C053437.packed 64 cuts53437 = true := by
 decide +kernel
def pointBounds53437 : List (Nat × Nat × Nat) := [(7008069632,112483068428371,112483456019992)]
theorem point_links_checked53437 : (cuts53437.take 1).map (fun c => (7008026625-1+2*2^10*c.k,112482994525650+c.lower,112483382117229+c.upper)) = pointBounds53437 := by
 decide +kernel
def cuts53438 : List PrefixCut := [⟨64,228851708,228851837⟩]
theorem checked53438 : checkPrefixCuts (2^48) 7008157697 10 Manual.Count131072.C053438.packed 64 cuts53438 = true := by
 decide +kernel
def pointBounds53438 : List (Nat × Nat × Nat) := [(7008288768,112483452193186,112483839785021)]
theorem point_links_checked53438 : (cuts53438.take 1).map (fun c => (7008157697-1+2*2^10*c.k,112483223341478+c.lower,112483610933184+c.upper)) = pointBounds53438 := by
 decide +kernel
def cuts53439 : List PrefixCut := [⟨64,231458007,231458138⟩]
theorem checked53439 : checkPrefixCuts (2^48) 7008288769 10 Manual.Count131072.C053439.packed 64 cuts53439 = true := by
 decide +kernel
def cuts53440 : List PrefixCut := [⟨43,158158496,158158587⟩,
⟨64,233542127,233542262⟩]
theorem checked53440 : checkPrefixCuts (2^48) 7008419841 10 Manual.Count131072.C053440.packed 64 cuts53440 = true := by
 decide +kernel
def pointBounds53440 : List (Nat × Nat × Nat) := [(7008507904,112483841809689,112484229401746)]
theorem point_links_checked53440 : (cuts53440.take 1).map (fun c => (7008419841-1+2*2^10*c.k,112483683651193+c.lower,112484071243159+c.upper)) = pointBounds53440 := by
 decide +kernel
def cuts53441 : List PrefixCut := [⟨64,229601949,229602077⟩]
theorem checked53441 : checkPrefixCuts (2^48) 7008550913 10 Manual.Count131072.C053441.packed 64 cuts53441 = true := by
 decide +kernel
def cuts53442 : List PrefixCut := [⟨22,79919909,79919959⟩,
⟨64,233694011,233694153⟩]
theorem checked53442 : checkPrefixCuts (2^48) 7008681985 10 Manual.Count131072.C053442.packed 64 cuts53442 = true := by
 decide +kernel
def pointBounds53442 : List (Nat × Nat × Nat) := [(7008727040,112484226715178,112484614307457)]
theorem point_links_checked53442 : (cuts53442.take 1).map (fun c => (7008681985-1+2*2^10*c.k,112484146795269+c.lower,112484534387498+c.upper)) = pointBounds53442 := by
 decide +kernel
def cuts53443 : List PrefixCut := [⟨64,234533016,234533148⟩]
theorem checked53443 : checkPrefixCuts (2^48) 7008813057 10 Manual.Count131072.C053443.packed 64 cuts53443 = true := by
 decide +kernel
def cuts53444 : List PrefixCut := [⟨1,3614344,3614346⟩,
⟨64,230512698,230512832⟩]
theorem checked53444 : checkPrefixCuts (2^48) 7008944129 10 Manual.Count131072.C053444.packed 64 cuts53444 = true := by
 decide +kernel
def pointBounds53444 : List (Nat × Nat × Nat) := [(7008946176,112484618636640,112485006229145)]
theorem point_links_checked53444 : (cuts53444.take 1).map (fun c => (7008944129-1+2*2^10*c.k,112484615022296+c.lower,112485002614799+c.upper)) = pointBounds53444 := by
 decide +kernel
def cuts53445 : List PrefixCut := [⟨44,157420837,157420925⟩,
⟨64,230508398,230508528⟩]
theorem checked53445 : checkPrefixCuts (2^48) 7009075201 10 Manual.Count131072.C053445.packed 64 cuts53445 = true := by
 decide +kernel
def pointBounds53445 : List (Nat × Nat × Nat) := [(7009165312,112485002955831,112485390548556)]
theorem point_links_checked53445 : (cuts53445.take 1).map (fun c => (7009075201-1+2*2^10*c.k,112484845534994+c.lower,112485233127631+c.upper)) = pointBounds53445 := by
 decide +kernel
def cuts53446 : List PrefixCut := [⟨64,228978130,228978260⟩]
theorem checked53446 : checkPrefixCuts (2^48) 7009206273 10 Manual.Count131072.C053446.packed 64 cuts53446 = true := by
 decide +kernel
def cuts53447 : List PrefixCut := [⟨23,82683260,82683306⟩,
⟨64,231584005,231584140⟩]
theorem checked53447 : checkPrefixCuts (2^48) 7009337345 10 Manual.Count131072.C053447.packed 64 cuts53447 = true := by
 decide +kernel
def pointBounds53447 : List (Nat × Nat × Nat) := [(7009384448,112485387704782,112485775297725)]
theorem point_links_checked53447 : (cuts53447.take 1).map (fun c => (7009337345-1+2*2^10*c.k,112485305021522+c.lower,112485692614419+c.upper)) = pointBounds53447 := by
 decide +kernel
def cuts53448 : List PrefixCut := [⟨64,228608150,228608278⟩]
theorem checked53448 : checkPrefixCuts (2^48) 7009468417 10 Manual.Count131072.C053448.packed 64 cuts53448 = true := by
 decide +kernel
def cuts53449 : List PrefixCut := [⟨2,6545366,6545370⟩,
⟨64,231735978,231736111⟩]
theorem checked53449 : checkPrefixCuts (2^48) 7009599489 10 Manual.Count131072.C053449.packed 64 cuts53449 = true := by
 decide +kernel
def pointBounds53449 : List (Nat × Nat × Nat) := [(7009603584,112485771759043,112486159352207)]
theorem point_links_checked53449 : (cuts53449.take 1).map (fun c => (7009599489-1+2*2^10*c.k,112485765213677+c.lower,112486152806837+c.upper)) = pointBounds53449 := by
 decide +kernel
def cuts53450 : List PrefixCut := [⟨45,163389133,163389226⟩,
⟨64,232855973,232856105⟩]
theorem checked53450 : checkPrefixCuts (2^48) 7009730561 10 Manual.Count131072.C053450.packed 64 cuts53450 = true := by
 decide +kernel
def pointBounds53450 : List (Nat × Nat × Nat) := [(7009822720,112486160338788,112486547932174)]
theorem point_links_checked53450 : (cuts53450.take 1).map (fun c => (7009730561-1+2*2^10*c.k,112485996949655+c.lower,112486384542948+c.upper)) = pointBounds53450 := by
 decide +kernel
def cuts53451 : List PrefixCut := [⟨64,231807617,231807750⟩]
theorem checked53451 : checkPrefixCuts (2^48) 7009861633 10 Manual.Count131072.C053451.packed 64 cuts53451 = true := by
 decide +kernel
def cuts53452 : List PrefixCut := [⟨24,87935593,87935643⟩,
⟨64,235497368,235497500⟩]
theorem checked53452 : checkPrefixCuts (2^48) 7009992705 10 Manual.Count131072.C053452.packed 64 cuts53452 = true := by
 decide +kernel
def pointBounds53452 : List (Nat × Nat × Nat) := [(7010041856,112486549548838,112486937142446)]
theorem point_links_checked53452 : (cuts53452.take 1).map (fun c => (7009992705-1+2*2^10*c.k,112486461613245+c.lower,112486849206803+c.upper)) = pointBounds53452 := by
 decide +kernel
def cuts53453 : List PrefixCut := [⟨64,230152699,230152829⟩]
theorem checked53453 : checkPrefixCuts (2^48) 7010123777 10 Manual.Count131072.C053453.packed 64 cuts53453 = true := by
 decide +kernel
def cuts53454 : List PrefixCut := [⟨3,10881154,10881160⟩,
⟨64,234524930,234525065⟩]
theorem checked53454 : checkPrefixCuts (2^48) 7010254849 10 Manual.Count131072.C053454.packed 64 cuts53454 = true := by
 decide +kernel
def pointBounds53454 : List (Nat × Nat × Nat) := [(7010260992,112486938144466,112487325738292)]
theorem point_links_checked53454 : (cuts53454.take 1).map (fun c => (7010254849-1+2*2^10*c.k,112486927263312+c.lower,112487314857132+c.upper)) = pointBounds53454 := by
 decide +kernel
def cuts53455 : List PrefixCut := [⟨46,168312398,168312494⟩,
⟨64,234199340,234199471⟩]
theorem checked53455 : checkPrefixCuts (2^48) 7010385921 10 Manual.Count131072.C053455.packed 64 cuts53455 = true := by
 decide +kernel
def pointBounds53455 : List (Nat × Nat × Nat) := [(7010480128,112487330100640,112487717694691)]
theorem point_links_checked53455 : (cuts53455.take 1).map (fun c => (7010385921-1+2*2^10*c.k,112487161788242+c.lower,112487549382197+c.upper)) = pointBounds53455 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000107
