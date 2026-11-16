import PlattAssemblyKernel
import PlattCertificates.Count131072.C042400
import PlattCertificates.Count131072.C042401
import PlattCertificates.Count131072.C042402
import PlattCertificates.Count131072.C042403
import PlattCertificates.Count131072.C042404
import PlattCertificates.Count131072.C042405
import PlattCertificates.Count131072.C042406
import PlattCertificates.Count131072.C042407
import PlattCertificates.Count131072.C042408
import PlattCertificates.Count131072.C042409
import PlattCertificates.Count131072.C042410
import PlattCertificates.Count131072.C042411
import PlattCertificates.Count131072.C042412
import PlattCertificates.Count131072.C042413
import PlattCertificates.Count131072.C042414
import PlattCertificates.Count131072.C042415
import PlattCertificates.Count131072.C042416
import PlattCertificates.Count131072.C042417
import PlattCertificates.Count131072.C042418
import PlattCertificates.Count131072.C042419
import PlattCertificates.Count131072.C042420
import PlattCertificates.Count131072.C042421
import PlattCertificates.Count131072.C042422
import PlattCertificates.Count131072.C042423
import PlattCertificates.Count131072.C042424
import PlattCertificates.Count131072.C042425
import PlattCertificates.Count131072.C042426
import PlattCertificates.Count131072.C042427
import PlattCertificates.Count131072.C042428
import PlattCertificates.Count131072.C042429
import PlattCertificates.Count131072.C042430
import PlattCertificates.Count131072.C042431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42400 : List PrefixCut := [⟨37,173244982,173245087⟩,
⟨64,297749110,297749287⟩]
theorem checked42400 : checkPrefixCuts (2^48) 5561384961 10 Manual.Count131072.C042400.packed 64 cuts42400 = true := by
 decide +kernel
def pointBounds42400 : List (Nat × Nat × Nat) := [(5561460736,109597706326215,109598092262967)]
theorem point_links_checked42400 : (cuts42400.take 1).map (fun c => (5561384961-1+2*2^10*c.k,109597533081233+c.lower,109597919017880+c.upper)) = pointBounds42400 := by
 decide +kernel
def cuts42401 : List PrefixCut := [⟨58,266768674,266768825⟩,
⟨64,295009078,295009246⟩]
theorem checked42401 : checkPrefixCuts (2^48) 5561516033 10 Manual.Count131072.C042401.packed 64 cuts42401 = true := by
 decide +kernel
def pointBounds42401 : List (Nat × Nat × Nat) := [(5561634816,109598097599017,109598483535992)]
theorem point_links_checked42401 : (cuts42401.take 1).map (fun c => (5561516033-1+2*2^10*c.k,109597830830343+c.lower,109598216767167+c.upper)) = pointBounds42401 := by
 decide +kernel
def cuts42402 : List PrefixCut := [⟨64,295913092,295913262⟩]
theorem checked42402 : checkPrefixCuts (2^48) 5561647105 10 Manual.Count131072.C042402.packed 64 cuts42402 = true := by
 decide +kernel
def cuts42403 : List PrefixCut := [⟨15,69435075,69435117⟩,
⟨64,293426338,293426512⟩]
theorem checked42403 : checkPrefixCuts (2^48) 5561778177 10 Manual.Count131072.C042403.packed 64 cuts42403 = true := by
 decide +kernel
def pointBounds42403 : List (Nat × Nat × Nat) := [(5561808896,109598491187588,109598877124792)]
theorem point_links_checked42403 : (cuts42403.take 1).map (fun c => (5561778177-1+2*2^10*c.k,109598421752513+c.lower,109598807689675+c.upper)) = pointBounds42403 := by
 decide +kernel
def cuts42404 : List PrefixCut := [⟨36,168066750,168066846⟩,
⟨64,298581360,298581531⟩]
theorem checked42404 : checkPrefixCuts (2^48) 5561909249 10 Manual.Count131072.C042404.packed 64 cuts42404 = true := by
 decide +kernel
def pointBounds42404 : List (Nat × Nat × Nat) := [(5561982976,109598883245601,109599269183033)]
theorem point_links_checked42404 : (cuts42404.take 1).map (fun c => (5561909249-1+2*2^10*c.k,109598715178851+c.lower,109599101116187+c.upper)) = pointBounds42404 := by
 decide +kernel
def cuts42405 : List PrefixCut := [⟨57,264769965,264770121⟩,
⟨64,295892213,295892388⟩]
theorem checked42405 : checkPrefixCuts (2^48) 5562040321 10 Manual.Count131072.C042405.packed 64 cuts42405 = true := by
 decide +kernel
def pointBounds42405 : List (Nat × Nat × Nat) := [(5562157056,109599278530176,109599664467839)]
theorem point_links_checked42405 : (cuts42405.take 1).map (fun c => (5562040321-1+2*2^10*c.k,109599013760211+c.lower,109599399697718+c.upper)) = pointBounds42405 := by
 decide +kernel
def cuts42406 : List PrefixCut := [⟨64,297302154,297302329⟩]
theorem checked42406 : checkPrefixCuts (2^48) 5562171393 10 Manual.Count131072.C042406.packed 64 cuts42406 = true := by
 decide +kernel
def cuts42407 : List PrefixCut := [⟨14,66797142,66797179⟩,
⟨64,296283092,296283267⟩]
theorem checked42407 : checkPrefixCuts (2^48) 5562302465 10 Manual.Count131072.C042407.packed 64 cuts42407 = true := by
 decide +kernel
def pointBounds42407 : List (Nat × Nat × Nat) := [(5562331136,109599673751720,109600059689614)]
theorem point_links_checked42407 : (cuts42407.take 1).map (fun c => (5562302465-1+2*2^10*c.k,109599606954578+c.lower,109599992892435+c.upper)) = pointBounds42407 := by
 decide +kernel
def cuts42408 : List PrefixCut := [⟨35,160612338,160612432⟩,
⟨64,293594167,293594341⟩]
theorem checked42408 : checkPrefixCuts (2^48) 5562433537 10 Manual.Count131072.C042408.packed 64 cuts42408 = true := by
 decide +kernel
def pointBounds42408 : List (Nat × Nat × Nat) := [(5562505216,109600063850008,109600449788134)]
theorem point_links_checked42408 : (cuts42408.take 1).map (fun c => (5562433537-1+2*2^10*c.k,109599903237670+c.lower,109600289175702+c.upper)) = pointBounds42408 := by
 decide +kernel
def cuts42409 : List PrefixCut := [⟨56,258065719,258065869⟩,
⟨64,296926922,296927093⟩]
theorem checked42409 : checkPrefixCuts (2^48) 5562564609 10 Manual.Count131072.C042409.packed 64 cuts42409 = true := by
 decide +kernel
def pointBounds42409 : List (Nat × Nat × Nat) := [(5562679296,109600454897556,109600840835912)]
theorem point_links_checked42409 : (cuts42409.take 1).map (fun c => (5562564609-1+2*2^10*c.k,109600196831837+c.lower,109600582770043+c.upper)) = pointBounds42409 := by
 decide +kernel
def cuts42410 : List PrefixCut := [⟨64,296464516,296464696⟩]
theorem checked42410 : checkPrefixCuts (2^48) 5562695681 10 Manual.Count131072.C042410.packed 64 cuts42410 = true := by
 decide +kernel
def cuts42411 : List PrefixCut := [⟨13,61326153,61326188⟩,
⟨64,297469510,297469681⟩]
theorem checked42411 : checkPrefixCuts (2^48) 5562826753 10 Manual.Count131072.C042411.packed 64 cuts42411 = true := by
 decide +kernel
def pointBounds42411 : List (Nat × Nat × Nat) := [(5562853376,109600851549428,109601237488020)]
theorem point_links_checked42411 : (cuts42411.take 1).map (fun c => (5562826753-1+2*2^10*c.k,109600790223275+c.lower,109601176161832+c.upper)) = pointBounds42411 := by
 decide +kernel
def cuts42412 : List PrefixCut := [⟨34,157966169,157966264⟩,
⟨64,295185638,295185815⟩]
theorem checked42412 : checkPrefixCuts (2^48) 5562957825 10 Manual.Count131072.C042412.packed 64 cuts42412 = true := by
 decide +kernel
def pointBounds42412 : List (Nat × Nat × Nat) := [(5563027456,109601245658954,109601631597777)]
theorem point_links_checked42412 : (cuts42412.take 1).map (fun c => (5562957825-1+2*2^10*c.k,109601087692785+c.lower,109601473631513+c.upper)) = pointBounds42412 := by
 decide +kernel
def cuts42413 : List PrefixCut := [⟨55,250957943,250958091⟩,
⟨64,293660765,293660939⟩]
theorem checked42413 : checkPrefixCuts (2^48) 5563088897 10 Manual.Count131072.C042413.packed 64 cuts42413 = true := by
 decide +kernel
def pointBounds42413 : List (Nat × Nat × Nat) := [(5563201536,109601633836366,109602019775419)]
theorem point_links_checked42413 : (cuts42413.take 1).map (fun c => (5563088897-1+2*2^10*c.k,109601382878423+c.lower,109601768817328+c.upper)) = pointBounds42413 := by
 decide +kernel
def cuts42414 : List PrefixCut := [⟨64,293299698,293299871⟩]
theorem checked42414 : checkPrefixCuts (2^48) 5563219969 10 Manual.Count131072.C042414.packed 64 cuts42414 = true := by
 decide +kernel
def cuts42415 : List PrefixCut := [⟨12,54439549,54439580⟩,
⟨64,293748113,293748281⟩]
theorem checked42415 : checkPrefixCuts (2^48) 5563351041 10 Manual.Count131072.C042415.packed 64 cuts42415 = true := by
 decide +kernel
def pointBounds42415 : List (Nat × Nat × Nat) := [(5563375616,109602024278435,109602410217718)]
theorem point_links_checked42415 : (cuts42415.take 1).map (fun c => (5563351041-1+2*2^10*c.k,109601969838886+c.lower,109602355778138+c.upper)) = pointBounds42415 := by
 decide +kernel
def cuts42416 : List PrefixCut := [⟨33,153802686,153802777⟩,
⟨64,298193369,298193545⟩]
theorem checked42416 : checkPrefixCuts (2^48) 5563482113 10 Manual.Count131072.C042416.packed 64 cuts42416 = true := by
 decide +kernel
def pointBounds42416 : List (Nat × Nat × Nat) := [(5563549696,109602417389685,109602803329196)]
theorem point_links_checked42416 : (cuts42416.take 1).map (fun c => (5563482113-1+2*2^10*c.k,109602263586999+c.lower,109602649526419+c.upper)) = pointBounds42416 := by
 decide +kernel
def cuts42417 : List PrefixCut := [⟨54,251389656,251389806⟩,
⟨64,297022744,297022919⟩]
theorem checked42417 : checkPrefixCuts (2^48) 5563613185 10 Manual.Count131072.C042417.packed 64 cuts42417 = true := by
 decide +kernel
def pointBounds42417 : List (Nat × Nat × Nat) := [(5563723776,109602813170024,109603199109770)]
theorem point_links_checked42417 : (cuts42417.take 1).map (fun c => (5563613185-1+2*2^10*c.k,109602561780368+c.lower,109602947719964+c.upper)) = pointBounds42417 := by
 decide +kernel
def cuts42418 : List PrefixCut := [⟨64,297926366,297926538⟩]
theorem checked42418 : checkPrefixCuts (2^48) 5563744257 10 Manual.Count131072.C042418.packed 64 cuts42418 = true := by
 decide +kernel
def cuts42419 : List PrefixCut := [⟨11,51854360,51854390⟩,
⟨64,294074599,294074769⟩]
theorem checked42419 : checkPrefixCuts (2^48) 5563875329 10 Manual.Count131072.C042419.packed 64 cuts42419 = true := by
 decide +kernel
def pointBounds42419 : List (Nat × Nat × Nat) := [(5563897856,109603208583838,109603594523811)]
theorem point_links_checked42419 : (cuts42419.take 1).map (fun c => (5563875329-1+2*2^10*c.k,109603156729478+c.lower,109603542669421+c.upper)) = pointBounds42419 := by
 decide +kernel
def cuts42420 : List PrefixCut := [⟨32,148223516,148223603⟩,
⟨64,296344093,296344272⟩]
theorem checked42420 : checkPrefixCuts (2^48) 5564006401 10 Manual.Count131072.C042420.packed 64 cuts42420 = true := by
 decide +kernel
def pointBounds42420 : List (Nat × Nat × Nat) := [(5564071936,109603599027593,109603984967793)]
theorem point_links_checked42420 : (cuts42420.take 1).map (fun c => (5564006401-1+2*2^10*c.k,109603450804077+c.lower,109603836744190+c.upper)) = pointBounds42420 := by
 decide +kernel
def cuts42421 : List PrefixCut := [⟨53,248988420,248988567⟩,
⟨64,300586390,300586569⟩]
theorem checked42421 : checkPrefixCuts (2^48) 5564137473 10 Manual.Count131072.C042421.packed 64 cuts42421 = true := by
 decide +kernel
def pointBounds42421 : List (Nat × Nat × Nat) := [(5564246016,109603996136590,109604382077029)]
theorem point_links_checked42421 : (cuts42421.take 1).map (fun c => (5564137473-1+2*2^10*c.k,109603747148170+c.lower,109604133088462+c.upper)) = pointBounds42421 := by
 decide +kernel
def cuts42422 : List PrefixCut := [⟨64,296481897,296482072⟩]
theorem checked42422 : checkPrefixCuts (2^48) 5564268545 10 Manual.Count131072.C042422.packed 64 cuts42422 = true := by
 decide +kernel
def cuts42423 : List PrefixCut := [⟨10,44362925,44362951⟩,
⟨64,292731668,292731843⟩]
theorem checked42423 : checkPrefixCuts (2^48) 5564399617 10 Manual.Count131072.C042423.packed 64 cuts42423 = true := by
 decide +kernel
def pointBounds42423 : List (Nat × Nat × Nat) := [(5564420096,109604388579382,109604774520054)]
theorem point_links_checked42423 : (cuts42423.take 1).map (fun c => (5564399617-1+2*2^10*c.k,109604344216457+c.lower,109604730157103+c.upper)) = pointBounds42423 := by
 decide +kernel
def cuts42424 : List PrefixCut := [⟨31,140116224,140116304⟩,
⟨64,288576969,288577139⟩]
theorem checked42424 : checkPrefixCuts (2^48) 5564530689 10 Manual.Count131072.C042424.packed 64 cuts42424 = true := by
 decide +kernel
def pointBounds42424 : List (Nat × Nat × Nat) := [(5564594176,109604777064349,109605163005250)]
theorem point_links_checked42424 : (cuts42424.take 1).map (fun c => (5564530689-1+2*2^10*c.k,109604636948125+c.lower,109605022888946+c.upper)) = pointBounds42424 := by
 decide +kernel
def cuts42425 : List PrefixCut := [⟨52,239050939,239051077⟩,
⟨64,296005699,296005873⟩]
theorem checked42425 : checkPrefixCuts (2^48) 5564661761 10 Manual.Count131072.C042425.packed 64 cuts42425 = true := by
 decide +kernel
def pointBounds42425 : List (Nat × Nat × Nat) := [(5564768256,109605164576033,109605550517162)]
theorem point_links_checked42425 : (cuts42425.take 1).map (fun c => (5564661761-1+2*2^10*c.k,109604925525094+c.lower,109605311466085+c.upper)) = pointBounds42425 := by
 decide +kernel
def cuts42426 : List PrefixCut := [⟨64,300146343,300146517⟩]
theorem checked42426 : checkPrefixCuts (2^48) 5564792833 10 Manual.Count131072.C042426.packed 64 cuts42426 = true := by
 decide +kernel
def cuts42427 : List PrefixCut := [⟨9,40716984,40717006⟩,
⟨64,297762044,297762218⟩]
theorem checked42427 : checkPrefixCuts (2^48) 5564923905 10 Manual.Count131072.C042427.packed 64 cuts42427 = true := by
 decide +kernel
def pointBounds42427 : List (Nat × Nat × Nat) := [(5564942336,109605562394120,109605948335481)]
theorem point_links_checked42427 : (cuts42427.take 1).map (fun c => (5564923905-1+2*2^10*c.k,109605521677136+c.lower,109605907618475+c.upper)) = pointBounds42427 := by
 decide +kernel
def cuts42428 : List PrefixCut := [⟨30,137472955,137473038⟩,
⟨64,290471769,290471943⟩]
theorem checked42428 : checkPrefixCuts (2^48) 5565054977 10 Manual.Count131072.C042428.packed 64 cuts42428 = true := by
 decide +kernel
def pointBounds42428 : List (Nat × Nat × Nat) := [(5565116416,109605956912135,109606342853731)]
theorem point_links_checked42428 : (cuts42428.take 1).map (fun c => (5565054977-1+2*2^10*c.k,109605819439180+c.lower,109606205380693+c.upper)) = pointBounds42428 := by
 decide +kernel
def cuts42429 : List PrefixCut := [⟨51,238016930,238017067⟩,
⟨64,297039979,297040152⟩]
theorem checked42429 : checkPrefixCuts (2^48) 5565186049 10 Manual.Count131072.C042429.packed 64 cuts42429 = true := by
 decide +kernel
def pointBounds42429 : List (Nat × Nat × Nat) := [(5565290496,109606347927879,109606733869703)]
theorem point_links_checked42429 : (cuts42429.take 1).map (fun c => (5565186049-1+2*2^10*c.k,109606109910949+c.lower,109606495852636+c.upper)) = pointBounds42429 := by
 decide +kernel
def cuts42430 : List PrefixCut := [⟨64,291975352,291975526⟩]
theorem checked42430 : checkPrefixCuts (2^48) 5565317121 10 Manual.Count131072.C042430.packed 64 cuts42430 = true := by
 decide +kernel
def cuts42431 : List PrefixCut := [⟨8,35857921,35857942⟩,
⟨64,293030544,293030718⟩]
theorem checked42431 : checkPrefixCuts (2^48) 5565448193 10 Manual.Count131072.C042431.packed 64 cuts42431 = true := by
 decide +kernel
def pointBounds42431 : List (Nat × Nat × Nat) := [(5565464576,109606734784201,109607120726256)]
theorem point_links_checked42431 : (cuts42431.take 1).map (fun c => (5565448193-1+2*2^10*c.k,109606698926280+c.lower,109607084868314+c.upper)) = pointBounds42431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000075
