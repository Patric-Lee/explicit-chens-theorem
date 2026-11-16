import PlattAssemblyKernel
import PlattCertificates.Count131072.C040448
import PlattCertificates.Count131072.C040449
import PlattCertificates.Count131072.C040450
import PlattCertificates.Count131072.C040451
import PlattCertificates.Count131072.C040452
import PlattCertificates.Count131072.C040453
import PlattCertificates.Count131072.C040454
import PlattCertificates.Count131072.C040455
import PlattCertificates.Count131072.C040456
import PlattCertificates.Count131072.C040457
import PlattCertificates.Count131072.C040458
import PlattCertificates.Count131072.C040459
import PlattCertificates.Count131072.C040460
import PlattCertificates.Count131072.C040461
import PlattCertificates.Count131072.C040462
import PlattCertificates.Count131072.C040463
import PlattCertificates.Count131072.C040464
import PlattCertificates.Count131072.C040465
import PlattCertificates.Count131072.C040466
import PlattCertificates.Count131072.C040467
import PlattCertificates.Count131072.C040468
import PlattCertificates.Count131072.C040469
import PlattCertificates.Count131072.C040470
import PlattCertificates.Count131072.C040471
import PlattCertificates.Count131072.C040472
import PlattCertificates.Count131072.C040473
import PlattCertificates.Count131072.C040474
import PlattCertificates.Count131072.C040475
import PlattCertificates.Count131072.C040476
import PlattCertificates.Count131072.C040477
import PlattCertificates.Count131072.C040478
import PlattCertificates.Count131072.C040479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40448 : List PrefixCut := [⟨29,142658956,142659040⟩,
⟨64,308234683,308234867⟩]
theorem checked40448 : checkPrefixCuts (2^48) 5305532417 10 Manual.Count131072.C040448.packed 64 cuts40448 = true := by
 decide +kernel
def pointBounds40448 : List (Nat × Nat × Nat) := [(5305591808,109006327512172,109006713100944)]
theorem point_links_checked40448 : (cuts40448.take 1).map (fun c => (5305532417-1+2*2^10*c.k,109006184853216+c.lower,109006570441904+c.upper)) = pointBounds40448 := by
 decide +kernel
def cuts40449 : List PrefixCut := [⟨46,223876501,223876635⟩,
⟨64,310561274,310561456⟩]
theorem checked40449 : checkPrefixCuts (2^48) 5305663489 10 Manual.Count131072.C040449.packed 64 cuts40449 = true := by
 decide +kernel
def pointBounds40449 : List (Nat × Nat × Nat) := [(5305757696,109006716964400,109007102553406)]
theorem point_links_checked40449 : (cuts40449.take 1).map (fun c => (5305663489-1+2*2^10*c.k,109006493087899+c.lower,109006878676771+c.upper)) = pointBounds40449 := by
 decide +kernel
def cuts40450 : List PrefixCut := [⟨63,304559058,304559239⟩,
⟨64,308749942,308750126⟩]
theorem checked40450 : checkPrefixCuts (2^48) 5305794561 10 Manual.Count131072.C040450.packed 64 cuts40450 = true := by
 decide +kernel
def pointBounds40450 : List (Nat × Nat × Nat) := [(5305923584,109007108208231,109007493797466)]
theorem point_links_checked40450 : (cuts40450.take 1).map (fun c => (5305794561-1+2*2^10*c.k,109006803649173+c.lower,109007189238227+c.upper)) = pointBounds40450 := by
 decide +kernel
def cuts40451 : List PrefixCut := [⟨64,309591047,309591229⟩]
theorem checked40451 : checkPrefixCuts (2^48) 5305925633 10 Manual.Count131072.C040451.packed 64 cuts40451 = true := by
 decide +kernel
def cuts40452 : List PrefixCut := [⟨16,77820955,77820999⟩,
⟨64,310166936,310167117⟩]
theorem checked40452 : checkPrefixCuts (2^48) 5306056705 10 Manual.Count131072.C040452.packed 64 cuts40452 = true := by
 decide +kernel
def pointBounds40452 : List (Nat × Nat × Nat) := [(5306089472,109007499811117,109007885400581)]
theorem point_links_checked40452 : (cuts40452.take 1).map (fun c => (5306056705-1+2*2^10*c.k,109007421990162+c.lower,109007807579582+c.upper)) = pointBounds40452 := by
 decide +kernel
def cuts40453 : List PrefixCut := [⟨33,161048272,161048367⟩,
⟨64,310477555,310477737⟩]
theorem checked40453 : checkPrefixCuts (2^48) 5306187777 10 Manual.Count131072.C040453.packed 64 cuts40453 = true := by
 decide +kernel
def pointBounds40453 : List (Nat × Nat × Nat) := [(5306255360,109007893205370,109008278795066)]
theorem point_links_checked40453 : (cuts40453.take 1).map (fun c => (5306187777-1+2*2^10*c.k,109007732157098+c.lower,109008117746699+c.upper)) = pointBounds40453 := by
 decide +kernel
def cuts40454 : List PrefixCut := [⟨50,239072527,239072670⟩,
⟨64,306438483,306438666⟩]
theorem checked40454 : checkPrefixCuts (2^48) 5306318849 10 Manual.Count131072.C040454.packed 64 cuts40454 = true := by
 decide +kernel
def pointBounds40454 : List (Nat × Nat × Nat) := [(5306421248,109008281707180,109008667297106)]
theorem point_links_checked40454 : (cuts40454.take 1).map (fun c => (5306318849-1+2*2^10*c.k,109008042634653+c.lower,109008428224436+c.upper)) = pointBounds40454 := by
 decide +kernel
def cuts40455 : List PrefixCut := [⟨64,315819591,315819777⟩]
theorem checked40455 : checkPrefixCuts (2^48) 5306449921 10 Manual.Count131072.C040455.packed 64 cuts40455 = true := by
 decide +kernel
def cuts40456 : List PrefixCut := [⟨3,15276261,15276270⟩,
⟨64,316448287,316448472⟩]
theorem checked40456 : checkPrefixCuts (2^48) 5306580993 10 Manual.Count131072.C040456.packed 64 cuts40456 = true := by
 decide +kernel
def pointBounds40456 : List (Nat × Nat × Nat) := [(5306587136,109008680168988,109009065759149)]
theorem point_links_checked40456 : (cuts40456.take 1).map (fun c => (5306580993-1+2*2^10*c.k,109008664892727+c.lower,109009050482879+c.upper)) = pointBounds40456 := by
 decide +kernel
def cuts40457 : List PrefixCut := [⟨20,96004378,96004435⟩,
⟨64,306734063,306734248⟩]
theorem checked40457 : checkPrefixCuts (2^48) 5306712065 10 Manual.Count131072.C040457.packed 64 cuts40457 = true := by
 decide +kernel
def pointBounds40457 : List (Nat × Nat × Nat) := [(5306753024,109009077345392,109009462935786)]
theorem point_links_checked40457 : (cuts40457.take 1).map (fun c => (5306712065-1+2*2^10*c.k,109008981341014+c.lower,109009366931351+c.upper)) = pointBounds40457 := by
 decide +kernel
def cuts40458 : List PrefixCut := [⟨37,178107018,178107120⟩,
⟨64,311765176,311765356⟩]
theorem checked40458 : checkPrefixCuts (2^48) 5306843137 10 Manual.Count131072.C040458.packed 64 cuts40458 = true := by
 decide +kernel
def pointBounds40458 : List (Nat × Nat × Nat) := [(5306918912,109009466182095,109009851772719)]
theorem point_links_checked40458 : (cuts40458.take 1).map (fun c => (5306843137-1+2*2^10*c.k,109009288075077+c.lower,109009673665599+c.upper)) = pointBounds40458 := by
 decide +kernel
def cuts40459 : List PrefixCut := [⟨54,261000616,261000770⟩,
⟨64,309264715,309264899⟩]
theorem checked40459 : checkPrefixCuts (2^48) 5306974209 10 Manual.Count131072.C040459.packed 64 cuts40459 = true := by
 decide +kernel
def pointBounds40459 : List (Nat × Nat × Nat) := [(5307084800,109009860840869,109010246431725)]
theorem point_links_checked40459 : (cuts40459.take 1).map (fun c => (5306974209-1+2*2^10*c.k,109009599840253+c.lower,109009985430955+c.upper)) = pointBounds40459 := by
 decide +kernel
def cuts40460 : List PrefixCut := [⟨64,308885798,308885983⟩]
theorem checked40460 : checkPrefixCuts (2^48) 5307105281 10 Manual.Count131072.C040460.packed 64 cuts40460 = true := by
 decide +kernel
def cuts40461 : List PrefixCut := [⟨7,33094455,33094475⟩,
⟨64,308188721,308188907⟩]
theorem checked40461 : checkPrefixCuts (2^48) 5307236353 10 Manual.Count131072.C040461.packed 64 cuts40461 = true := by
 decide +kernel
def pointBounds40461 : List (Nat × Nat × Nat) := [(5307250688,109010251085221,109010636676312)]
theorem point_links_checked40461 : (cuts40461.take 1).map (fun c => (5307236353-1+2*2^10*c.k,109010217990766+c.lower,109010603581837+c.upper)) = pointBounds40461 := by
 decide +kernel
def cuts40462 : List PrefixCut := [⟨24,115190944,115191012⟩,
⟨64,306431012,306431192⟩]
theorem checked40462 : checkPrefixCuts (2^48) 5307367425 10 Manual.Count131072.C040462.packed 64 cuts40462 = true := by
 decide +kernel
def pointBounds40462 : List (Nat × Nat × Nat) := [(5307416576,109010641370431,109011026961756)]
theorem point_links_checked40462 : (cuts40462.take 1).map (fun c => (5307367425-1+2*2^10*c.k,109010526179487+c.lower,109010911770744+c.upper)) = pointBounds40462 := by
 decide +kernel
def cuts40463 : List PrefixCut := [⟨41,196487337,196487452⟩,
⟨64,309022009,309022190⟩]
theorem checked40463 : checkPrefixCuts (2^48) 5307498497 10 Manual.Count131072.C040463.packed 64 cuts40463 = true := by
 decide +kernel
def pointBounds40463 : List (Nat × Nat × Nat) := [(5307582464,109011029097836,109011414689388)]
theorem point_links_checked40463 : (cuts40463.take 1).map (fun c => (5307498497-1+2*2^10*c.k,109010832610499+c.lower,109011218201936+c.upper)) = pointBounds40463 := by
 decide +kernel
def cuts40464 : List PrefixCut := [⟨58,278468582,278468744⟩,
⟨64,308059813,308059991⟩]
theorem checked40464 : checkPrefixCuts (2^48) 5307629569 10 Manual.Count131072.C040464.packed 64 cuts40464 = true := by
 decide +kernel
def pointBounds40464 : List (Nat × Nat × Nat) := [(5307748352,109011420101090,109011805692870)]
theorem point_links_checked40464 : (cuts40464.take 1).map (fun c => (5307629569-1+2*2^10*c.k,109011141632508+c.lower,109011527224126+c.upper)) = pointBounds40464 := by
 decide +kernel
def cuts40465 : List PrefixCut := [⟨64,310650720,310650905⟩]
theorem checked40465 : checkPrefixCuts (2^48) 5307760641 10 Manual.Count131072.C040465.packed 64 cuts40465 = true := by
 decide +kernel
def cuts40466 : List PrefixCut := [⟨11,54408160,54408191⟩,
⟨64,310430940,310431119⟩]
theorem checked40466 : checkPrefixCuts (2^48) 5307891713 10 Manual.Count131072.C040466.packed 64 cuts40466 = true := by
 decide +kernel
def pointBounds40466 : List (Nat × Nat × Nat) := [(5307914240,109011814751201,109012200343213)]
theorem point_links_checked40466 : (cuts40466.take 1).map (fun c => (5307891713-1+2*2^10*c.k,109011760343041+c.lower,109012145935022+c.upper)) = pointBounds40466 := by
 decide +kernel
def cuts40467 : List PrefixCut := [⟨28,134690900,134690982⟩,
⟨64,309203626,309203814⟩]
theorem checked40467 : checkPrefixCuts (2^48) 5308022785 10 Manual.Count131072.C040467.packed 64 cuts40467 = true := by
 decide +kernel
def pointBounds40467 : List (Nat × Nat × Nat) := [(5308080128,109012205464881,109012591057123)]
theorem point_links_checked40467 : (cuts40467.take 1).map (fun c => (5308022785-1+2*2^10*c.k,109012070773981+c.lower,109012456366141+c.upper)) = pointBounds40467 := by
 decide +kernel
def cuts40468 : List PrefixCut := [⟨45,216772061,216772191⟩,
⟨64,307711266,307711448⟩]
theorem checked40468 : checkPrefixCuts (2^48) 5308153857 10 Manual.Count131072.C040468.packed 64 cuts40468 = true := by
 decide +kernel
def pointBounds40468 : List (Nat × Nat × Nat) := [(5308246016,109012596749668,109012982342146)]
theorem point_links_checked40468 : (cuts40468.take 1).map (fun c => (5308153857-1+2*2^10*c.k,109012379977607+c.lower,109012765569955+c.upper)) = pointBounds40468 := by
 decide +kernel
def cuts40469 : List PrefixCut := [⟨62,299272786,299272966⟩,
⟨64,310460912,310461098⟩]
theorem checked40469 : checkPrefixCuts (2^48) 5308284929 10 Manual.Count131072.C040469.packed 64 cuts40469 = true := by
 decide +kernel
def pointBounds40469 : List (Nat × Nat × Nat) := [(5308411904,109012986961659,109013372554369)]
theorem point_links_checked40469 : (cuts40469.take 1).map (fun c => (5308284929-1+2*2^10*c.k,109012687688873+c.lower,109013073281403+c.upper)) = pointBounds40469 := by
 decide +kernel
def cuts40470 : List PrefixCut := [⟨64,312521195,312521381⟩]
theorem checked40470 : checkPrefixCuts (2^48) 5308416001 10 Manual.Count131072.C040470.packed 64 cuts40470 = true := by
 decide +kernel
def cuts40471 : List PrefixCut := [⟨15,71156608,71156650⟩,
⟨64,314316225,314316405⟩]
theorem checked40471 : checkPrefixCuts (2^48) 5308547073 10 Manual.Count131072.C040471.packed 64 cuts40471 = true := by
 decide +kernel
def pointBounds40471 : List (Nat × Nat × Nat) := [(5308577792,109013381827588,109013767420532)]
theorem point_links_checked40471 : (cuts40471.take 1).map (fun c => (5308547073-1+2*2^10*c.k,109013310670980+c.lower,109013696263882+c.upper)) = pointBounds40471 := by
 decide +kernel
def cuts40472 : List PrefixCut := [⟨33,159116964,159117059⟩,
⟨64,310066789,310066971⟩]
theorem checked40472 : checkPrefixCuts (2^48) 5308678145 10 Manual.Count131072.C040472.packed 64 cuts40472 = true := by
 decide +kernel
def pointBounds40472 : List (Nat × Nat × Nat) := [(5308745728,109013784104169,109014169697346)]
theorem point_links_checked40472 : (cuts40472.take 1).map (fun c => (5308678145-1+2*2^10*c.k,109013624987205+c.lower,109014010580287+c.upper)) = pointBounds40472 := by
 decide +kernel
def cuts40473 : List PrefixCut := [⟨51,246648235,246648380⟩,
⟨64,309688029,309688212⟩]
theorem checked40473 : checkPrefixCuts (2^48) 5308809217 10 Manual.Count131072.C040473.packed 64 cuts40473 = true := by
 decide +kernel
def pointBounds40473 : List (Nat × Nat × Nat) := [(5308913664,109014181702229,109014567295638)]
theorem point_links_checked40473 : (cuts40473.take 1).map (fun c => (5308809217-1+2*2^10*c.k,109013935053994+c.lower,109014320647258+c.upper)) = pointBounds40473 := by
 decide +kernel
def cuts40474 : List PrefixCut := [⟨64,306499259,306499441⟩]
theorem checked40474 : checkPrefixCuts (2^48) 5308940289 10 Manual.Count131072.C040474.packed 64 cuts40474 = true := by
 decide +kernel
def cuts40475 : List PrefixCut := [⟨5,24335112,24335126⟩,
⟨64,311846424,311846607⟩]
theorem checked40475 : checkPrefixCuts (2^48) 5309071361 10 Manual.Count131072.C040475.packed 64 cuts40475 = true := by
 decide +kernel
def pointBounds40475 : List (Nat × Nat × Nat) := [(5309081600,109014575576394,109014961170037)]
theorem point_links_checked40475 : (cuts40475.take 1).map (fun c => (5309071361-1+2*2^10*c.k,109014551241282+c.lower,109014936834911+c.upper)) = pointBounds40475 := by
 decide +kernel
def cuts40476 : List PrefixCut := [⟨23,114037811,114037875⟩,
⟨64,310672395,310672576⟩]
theorem checked40476 : checkPrefixCuts (2^48) 5309202433 10 Manual.Count131072.C040476.packed 64 cuts40476 = true := by
 decide +kernel
def pointBounds40476 : List (Nat × Nat × Nat) := [(5309249536,109014977125517,109015362719393)]
theorem point_links_checked40476 : (cuts40476.take 1).map (fun c => (5309202433-1+2*2^10*c.k,109014863087706+c.lower,109015248681518+c.upper)) = pointBounds40476 := by
 decide +kernel
def cuts40477 : List PrefixCut := [⟨41,198168909,198169025⟩,
⟨64,308226037,308226218⟩]
theorem checked40477 : checkPrefixCuts (2^48) 5309333505 10 Manual.Count131072.C040477.packed 64 cuts40477 = true := by
 decide +kernel
def pointBounds40477 : List (Nat × Nat × Nat) := [(5309417472,109015371929010,109015757523119)]
theorem point_links_checked40477 : (cuts40477.take 1).map (fun c => (5309333505-1+2*2^10*c.k,109015173760101+c.lower,109015559354094+c.upper)) = pointBounds40477 := by
 decide +kernel
def cuts40478 : List PrefixCut := [⟨59,285741126,285741296⟩,
⟨64,310073882,310074068⟩]
theorem checked40478 : checkPrefixCuts (2^48) 5309464577 10 Manual.Count131072.C040478.packed 64 cuts40478 = true := by
 decide +kernel
def pointBounds40478 : List (Nat × Nat × Nat) := [(5309585408,109015767727264,109016153321608)]
theorem point_links_checked40478 : (cuts40478.take 1).map (fun c => (5309464577-1+2*2^10*c.k,109015481986138+c.lower,109015867580312+c.upper)) = pointBounds40478 := by
 decide +kernel
def cuts40479 : List PrefixCut := [⟨64,311603547,311603730⟩]
theorem checked40479 : checkPrefixCuts (2^48) 5309595649 10 Manual.Count131072.C040479.packed 64 cuts40479 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000014
