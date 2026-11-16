import PlattAssemblyKernel
import PlattCertificates.Count131072.C073392
import PlattCertificates.Count131072.C073393
import PlattCertificates.Count131072.C073394
import PlattCertificates.Count131072.C073395
import PlattCertificates.Count131072.C073396
import PlattCertificates.Count131072.C073397
import PlattCertificates.Count131072.C073398
import PlattCertificates.Count131072.C073399
import PlattCertificates.Count131072.C073400
import PlattCertificates.Count131072.C073401
import PlattCertificates.Count131072.C073402
import PlattCertificates.Count131072.C073403
import PlattCertificates.Count131072.C073404
import PlattCertificates.Count131072.C073405
import PlattCertificates.Count131072.C073406
import PlattCertificates.Count131072.C073407
import PlattCertificates.Count131072.C073408
import PlattCertificates.Count131072.C073409
import PlattCertificates.Count131072.C073410
import PlattCertificates.Count131072.C073411
import PlattCertificates.Count131072.C073412
import PlattCertificates.Count131072.C073413
import PlattCertificates.Count131072.C073414
import PlattCertificates.Count131072.C073415
import PlattCertificates.Count131072.C073416
import PlattCertificates.Count131072.C073417
import PlattCertificates.Count131072.C073418
import PlattCertificates.Count131072.C073419
import PlattCertificates.Count131072.C073420
import PlattCertificates.Count131072.C073421
import PlattCertificates.Count131072.C073422
import PlattCertificates.Count131072.C073423
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73392 : List PrefixCut := [⟨64,168879669,168879772⟩]
theorem checked73392 : checkPrefixCuts (2^48) 9623568385 10 Manual.Count131072.C073392.packed 64 cuts73392 = true := by
 decide +kernel
def cuts73393 : List PrefixCut := [⟨8,20912372,20912385⟩,
⟨64,167853686,167853788⟩]
theorem checked73393 : checkPrefixCuts (2^48) 9623699457 10 Manual.Count131072.C073393.packed 64 cuts73393 = true := by
 decide +kernel
def pointBounds73393 : List (Nat × Nat × Nat) := [(9623715840,116393721882744,116394111731675)]
theorem point_links_checked73393 : (cuts73393.take 1).map (fun c => (9623699457-1+2*2^10*c.k,116393700970372+c.lower,116394090819290+c.upper)) = pointBounds73393 := by
 decide +kernel
def cuts73394 : List PrefixCut := [⟨64,166272042,166272134⟩]
theorem checked73394 : checkPrefixCuts (2^48) 9623830529 10 Manual.Count131072.C073394.packed 64 cuts73394 = true := by
 decide +kernel
def cuts73395 : List PrefixCut := [⟨27,70310303,70310351⟩,
⟨64,165421596,165421705⟩]
theorem checked73395 : checkPrefixCuts (2^48) 9623961601 10 Manual.Count131072.C073395.packed 64 cuts73395 = true := by
 decide +kernel
def pointBounds73395 : List (Nat × Nat × Nat) := [(9624016896,116394105406403,116394495255563)]
theorem point_links_checked73395 : (cuts73395.take 1).map (fun c => (9623961601-1+2*2^10*c.k,116394035096100+c.lower,116394424945212+c.upper)) = pointBounds73395 := by
 decide +kernel
def cuts73396 : List PrefixCut := [⟨64,166910931,166911034⟩]
theorem checked73396 : checkPrefixCuts (2^48) 9624092673 10 Manual.Count131072.C073396.packed 64 cuts73396 = true := by
 decide +kernel
def cuts73397 : List PrefixCut := [⟨46,122308283,122308353⟩,
⟨64,168692696,168692788⟩]
theorem checked73397 : checkPrefixCuts (2^48) 9624223745 10 Manual.Count131072.C073397.packed 64 cuts73397 = true := by
 decide +kernel
def pointBounds73397 : List (Nat × Nat × Nat) := [(9624317952,116394489736910,116394879586304)]
theorem point_links_checked73397 : (cuts73397.take 1).map (fun c => (9624223745-1+2*2^10*c.k,116394367428627+c.lower,116394757277951+c.upper)) = pointBounds73397 := by
 decide +kernel
def cuts73398 : List PrefixCut := [⟨64,166262980,166263077⟩]
theorem checked73398 : checkPrefixCuts (2^48) 9624354817 10 Manual.Count131072.C073398.packed 64 cuts73398 = true := by
 decide +kernel
def cuts73399 : List PrefixCut := [⟨64,166523922,166524022⟩]
theorem checked73399 : checkPrefixCuts (2^48) 9624485889 10 Manual.Count131072.C073399.packed 64 cuts73399 = true := by
 decide +kernel
def cuts73400 : List PrefixCut := [⟨1,2573587,2573588⟩,
⟨64,167515987,167516086⟩]
theorem checked73400 : checkPrefixCuts (2^48) 9624616961 10 Manual.Count131072.C073400.packed 64 cuts73400 = true := by
 decide +kernel
def pointBounds73400 : List (Nat × Nat × Nat) := [(9624619008,116394871481812,116395261331426)]
theorem point_links_checked73400 : (cuts73400.take 1).map (fun c => (9624616961-1+2*2^10*c.k,116394868908225+c.lower,116395258757838+c.upper)) = pointBounds73400 := by
 decide +kernel
def cuts73401 : List PrefixCut := [⟨64,165437338,165437438⟩]
theorem checked73401 : checkPrefixCuts (2^48) 9624748033 10 Manual.Count131072.C073401.packed 64 cuts73401 = true := by
 decide +kernel
def cuts73402 : List PrefixCut := [⟨20,52873967,52873998⟩,
⟨64,167745389,167745487⟩]
theorem checked73402 : checkPrefixCuts (2^48) 9624879105 10 Manual.Count131072.C073402.packed 64 cuts73402 = true := by
 decide +kernel
def pointBounds73402 : List (Nat × Nat × Nat) := [(9624920064,116395254735517,116395644585360)]
theorem point_links_checked73402 : (cuts73402.take 1).map (fun c => (9624879105-1+2*2^10*c.k,116395201861550+c.lower,116395591711362+c.upper)) = pointBounds73402 := by
 decide +kernel
def cuts73403 : List PrefixCut := [⟨64,165169631,165169734⟩]
theorem checked73403 : checkPrefixCuts (2^48) 9625010177 10 Manual.Count131072.C073403.packed 64 cuts73403 = true := by
 decide +kernel
def cuts73404 : List PrefixCut := [⟨39,102206367,102206424⟩,
⟨64,167770057,167770156⟩]
theorem checked73404 : checkPrefixCuts (2^48) 9625141249 10 Manual.Count131072.C073404.packed 64 cuts73404 = true := by
 decide +kernel
def pointBounds73404 : List (Nat × Nat × Nat) := [(9625221120,116395636982937,116396026833007)]
theorem point_links_checked73404 : (cuts73404.take 1).map (fun c => (9625141249-1+2*2^10*c.k,116395534776570+c.lower,116395924626583+c.upper)) = pointBounds73404 := by
 decide +kernel
def cuts73405 : List PrefixCut := [⟨64,165574535,165574639⟩]
theorem checked73405 : checkPrefixCuts (2^48) 9625272321 10 Manual.Count131072.C073405.packed 64 cuts73405 = true := by
 decide +kernel
def cuts73406 : List PrefixCut := [⟨58,151418911,151419004⟩,
⟨64,166888214,166888318⟩]
theorem checked73406 : checkPrefixCuts (2^48) 9625403393 10 Manual.Count131072.C073406.packed 64 cuts73406 = true := by
 decide +kernel
def pointBounds73406 : List (Nat × Nat × Nat) := [(9625522176,116396019540073,116396409390382)]
theorem point_links_checked73406 : (cuts73406.take 1).map (fun c => (9625403393-1+2*2^10*c.k,116395868121162+c.lower,116396257971378+c.upper)) = pointBounds73406 := by
 decide +kernel
def cuts73407 : List PrefixCut := [⟨64,165394576,165394679⟩]
theorem checked73407 : checkPrefixCuts (2^48) 9625534465 10 Manual.Count131072.C073407.packed 64 cuts73407 = true := by
 decide +kernel
def cuts73408 : List PrefixCut := [⟨64,167439248,167439350⟩]
theorem checked73408 : checkPrefixCuts (2^48) 9625665537 10 Manual.Count131072.C073408.packed 64 cuts73408 = true := by
 decide +kernel
def cuts73409 : List PrefixCut := [⟨13,33569452,33569473⟩,
⟨64,166384277,166384378⟩]
theorem checked73409 : checkPrefixCuts (2^48) 9625796609 10 Manual.Count131072.C073409.packed 64 cuts73409 = true := by
 decide +kernel
def pointBounds73409 : List (Nat × Nat × Nat) := [(9625823232,116396401412652,116396791263198)]
theorem point_links_checked73409 : (cuts73409.take 1).map (fun c => (9625796609-1+2*2^10*c.k,116396367843200+c.lower,116396757693725+c.upper)) = pointBounds73409 := by
 decide +kernel
def cuts73410 : List PrefixCut := [⟨64,167961035,167961136⟩]
theorem checked73410 : checkPrefixCuts (2^48) 9625927681 10 Manual.Count131072.C073410.packed 64 cuts73410 = true := by
 decide +kernel
def cuts73411 : List PrefixCut := [⟨32,82868507,82868561⟩,
⟨64,166204302,166204407⟩]
theorem checked73411 : checkPrefixCuts (2^48) 9626058753 10 Manual.Count131072.C073411.packed 64 cuts73411 = true := by
 decide +kernel
def pointBounds73411 : List (Nat × Nat × Nat) := [(9626124288,116396785057019,116397174907800)]
theorem point_links_checked73411 : (cuts73411.take 1).map (fun c => (9626058753-1+2*2^10*c.k,116396702188512+c.lower,116397092039239+c.upper)) = pointBounds73411 := by
 decide +kernel
def cuts73412 : List PrefixCut := [⟨64,170383406,170383510⟩]
theorem checked73412 : checkPrefixCuts (2^48) 9626189825 10 Manual.Count131072.C073412.packed 64 cuts73412 = true := by
 decide +kernel
def cuts73413 : List PrefixCut := [⟨51,133714391,133714471⟩,
⟨64,167223173,167223272⟩]
theorem checked73413 : checkPrefixCuts (2^48) 9626320897 10 Manual.Count131072.C073413.packed 64 cuts73413 = true := by
 decide +kernel
def pointBounds73413 : List (Nat × Nat × Nat) := [(9626425344,116397172490611,116397562341627)]
theorem point_links_checked73413 : (cuts73413.take 1).map (fun c => (9626320897-1+2*2^10*c.k,116397038776220+c.lower,116397428627156+c.upper)) = pointBounds73413 := by
 decide +kernel
def cuts73414 : List PrefixCut := [⟨64,167717968,167718076⟩]
theorem checked73414 : checkPrefixCuts (2^48) 9626451969 10 Manual.Count131072.C073414.packed 64 cuts73414 = true := by
 decide +kernel
def cuts73415 : List PrefixCut := [⟨64,166809263,166809360⟩]
theorem checked73415 : checkPrefixCuts (2^48) 9626583041 10 Manual.Count131072.C073415.packed 64 cuts73415 = true := by
 decide +kernel
def cuts73416 : List PrefixCut := [⟨6,14560982,14560991⟩,
⟨64,166865477,166865574⟩]
theorem checked73416 : checkPrefixCuts (2^48) 9626714113 10 Manual.Count131072.C073416.packed 64 cuts73416 = true := by
 decide +kernel
def pointBounds73416 : List (Nat × Nat × Nat) := [(9626726400,116397555087606,116397944938855)]
theorem point_links_checked73416 : (cuts73416.take 1).map (fun c => (9626714113-1+2*2^10*c.k,116397540526624+c.lower,116397930377864+c.upper)) = pointBounds73416 := by
 decide +kernel
def cuts73417 : List PrefixCut := [⟨64,166015288,166015385⟩]
theorem checked73417 : checkPrefixCuts (2^48) 9626845185 10 Manual.Count131072.C073417.packed 64 cuts73417 = true := by
 decide +kernel
def cuts73418 : List PrefixCut := [⟨25,65844121,65844160⟩,
⟨64,167621129,167621228⟩]
theorem checked73418 : checkPrefixCuts (2^48) 9626976257 10 Manual.Count131072.C073418.packed 64 cuts73418 = true := by
 decide +kernel
def pointBounds73418 : List (Nat × Nat × Nat) := [(9627027456,116397939251510,116398329102983)]
theorem point_links_checked73418 : (cuts73418.take 1).map (fun c => (9626976257-1+2*2^10*c.k,116397873407389+c.lower,116398263258823+c.upper)) = pointBounds73418 := by
 decide +kernel
def cuts73419 : List PrefixCut := [⟨64,167267992,167268089⟩]
theorem checked73419 : checkPrefixCuts (2^48) 9627107329 10 Manual.Count131072.C073419.packed 64 cuts73419 = true := by
 decide +kernel
def cuts73420 : List PrefixCut := [⟨44,113352658,113352729⟩,
⟨64,165950036,165950136⟩]
theorem checked73420 : checkPrefixCuts (2^48) 9627238401 10 Manual.Count131072.C073420.packed 64 cuts73420 = true := by
 decide +kernel
def pointBounds73420 : List (Nat × Nat × Nat) := [(9627328512,116398321649168,116398711500869)]
theorem point_links_checked73420 : (cuts73420.take 1).map (fun c => (9627238401-1+2*2^10*c.k,116398208296510+c.lower,116398598148140+c.upper)) = pointBounds73420 := by
 decide +kernel
def cuts73421 : List PrefixCut := [⟨64,169339243,169339343⟩]
theorem checked73421 : checkPrefixCuts (2^48) 9627369473 10 Manual.Count131072.C073421.packed 64 cuts73421 = true := by
 decide +kernel
def cuts73422 : List PrefixCut := [⟨63,165302340,165302437⟩,
⟨64,168079775,168079873⟩]
theorem checked73422 : checkPrefixCuts (2^48) 9627500545 10 Manual.Count131072.C073422.packed 64 cuts73422 = true := by
 decide +kernel
def pointBounds73422 : List (Nat × Nat × Nat) := [(9627629568,116398708888129,116399098740056)]
theorem point_links_checked73422 : (cuts73422.take 1).map (fun c => (9627500545-1+2*2^10*c.k,116398543585789+c.lower,116398933437619+c.upper)) = pointBounds73422 := by
 decide +kernel
def cuts73423 : List PrefixCut := [⟨64,165767841,165767944⟩]
theorem checked73423 : checkPrefixCuts (2^48) 9627631617 10 Manual.Count131072.C073423.packed 64 cuts73423 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000106
