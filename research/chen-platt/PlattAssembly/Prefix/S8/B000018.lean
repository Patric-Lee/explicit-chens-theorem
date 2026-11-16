import PlattAssemblyKernel
import PlattCertificates.Count131072.C070576
import PlattCertificates.Count131072.C070577
import PlattCertificates.Count131072.C070578
import PlattCertificates.Count131072.C070579
import PlattCertificates.Count131072.C070580
import PlattCertificates.Count131072.C070581
import PlattCertificates.Count131072.C070582
import PlattCertificates.Count131072.C070583
import PlattCertificates.Count131072.C070584
import PlattCertificates.Count131072.C070585
import PlattCertificates.Count131072.C070586
import PlattCertificates.Count131072.C070587
import PlattCertificates.Count131072.C070588
import PlattCertificates.Count131072.C070589
import PlattCertificates.Count131072.C070590
import PlattCertificates.Count131072.C070591
import PlattCertificates.Count131072.C070592
import PlattCertificates.Count131072.C070593
import PlattCertificates.Count131072.C070594
import PlattCertificates.Count131072.C070595
import PlattCertificates.Count131072.C070596
import PlattCertificates.Count131072.C070597
import PlattCertificates.Count131072.C070598
import PlattCertificates.Count131072.C070599
import PlattCertificates.Count131072.C070600
import PlattCertificates.Count131072.C070601
import PlattCertificates.Count131072.C070602
import PlattCertificates.Count131072.C070603
import PlattCertificates.Count131072.C070604
import PlattCertificates.Count131072.C070605
import PlattCertificates.Count131072.C070606
import PlattCertificates.Count131072.C070607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70576 : List PrefixCut := [⟨64,174793885,174793988⟩]
theorem checked70576 : checkPrefixCuts (2^48) 9254469633 10 Manual.Count131072.C070576.packed 64 cuts70576 = true := by
 decide +kernel
def cuts70577 : List PrefixCut := [⟨33,91121780,91121836⟩,
⟨64,173848582,173848684⟩]
theorem checked70577 : checkPrefixCuts (2^48) 9254600705 10 Manual.Count131072.C070577.packed 64 cuts70577 = true := by
 decide +kernel
def pointBounds70577 : List (Nat × Nat × Nat) := [(9254668288,115914501787363,115914891351856)]
theorem point_links_checked70577 : (cuts70577.take 1).map (fun c => (9254600705-1+2*2^10*c.k,115914410665583+c.lower,115914800230020+c.upper)) = pointBounds70577 := by
 decide +kernel
def cuts70578 : List PrefixCut := [⟨64,172142929,172143031⟩]
theorem checked70578 : checkPrefixCuts (2^48) 9254731777 10 Manual.Count131072.C070578.packed 64 cuts70578 = true := by
 decide +kernel
def cuts70579 : List PrefixCut := [⟨47,125973006,125973083⟩,
⟨64,171897171,171897276⟩]
theorem checked70579 : checkPrefixCuts (2^48) 9254862849 10 Manual.Count131072.C070579.packed 64 cuts70579 = true := by
 decide +kernel
def pointBounds70579 : List (Nat × Nat × Nat) := [(9254959104,115914882630100,115915272194818)]
theorem point_links_checked70579 : (cuts70579.take 1).map (fun c => (9254862849-1+2*2^10*c.k,115914756657094+c.lower,115915146221735+c.upper)) = pointBounds70579 := by
 decide +kernel
def cuts70580 : List PrefixCut := [⟨64,174023668,174023772⟩]
theorem checked70580 : checkPrefixCuts (2^48) 9254993921 10 Manual.Count131072.C070580.packed 64 cuts70580 = true := by
 decide +kernel
def cuts70581 : List PrefixCut := [⟨61,168546971,168547078⟩,
⟨64,176210908,176211020⟩]
theorem checked70581 : checkPrefixCuts (2^48) 9255124993 10 Manual.Count131072.C070581.packed 64 cuts70581 = true := by
 decide +kernel
def pointBounds70581 : List (Nat × Nat × Nat) := [(9255249920,115915271124904,115915660689861)]
theorem point_links_checked70581 : (cuts70581.take 1).map (fun c => (9255124993-1+2*2^10*c.k,115915102577933+c.lower,115915492142783+c.upper)) = pointBounds70581 := by
 decide +kernel
def cuts70582 : List PrefixCut := [⟨64,171950713,171950806⟩]
theorem checked70582 : checkPrefixCuts (2^48) 9255256065 10 Manual.Count131072.C070582.packed 64 cuts70582 = true := by
 decide +kernel
def cuts70583 : List PrefixCut := [⟨64,174320381,174320484⟩]
theorem checked70583 : checkPrefixCuts (2^48) 9255387137 10 Manual.Count131072.C070583.packed 64 cuts70583 = true := by
 decide +kernel
def cuts70584 : List PrefixCut := [⟨11,28586846,28586864⟩,
⟨64,171732954,171733052⟩]
theorem checked70584 : checkPrefixCuts (2^48) 9255518209 10 Manual.Count131072.C070584.packed 64 cuts70584 = true := by
 decide +kernel
def pointBounds70584 : List (Nat × Nat × Nat) := [(9255540736,115915653646781,115916043211957)]
theorem point_links_checked70584 : (cuts70584.take 1).map (fun c => (9255518209-1+2*2^10*c.k,115915625059935+c.lower,115916014625093+c.upper)) = pointBounds70584 := by
 decide +kernel
def cuts70585 : List PrefixCut := [⟨64,175562300,175562401⟩]
theorem checked70585 : checkPrefixCuts (2^48) 9255649281 10 Manual.Count131072.C070585.packed 64 cuts70585 = true := by
 decide +kernel
def cuts70586 : List PrefixCut := [⟨25,67633243,67633285⟩,
⟨64,171302348,171302451⟩]
theorem checked70586 : checkPrefixCuts (2^48) 9255780353 10 Manual.Count131072.C070586.packed 64 cuts70586 = true := by
 decide +kernel
def pointBounds70586 : List (Nat × Nat × Nat) := [(9255831552,115916039988432,115916429553831)]
theorem point_links_checked70586 : (cuts70586.take 1).map (fun c => (9255780353-1+2*2^10*c.k,115915972355189+c.lower,115916361920546+c.upper)) = pointBounds70586 := by
 decide +kernel
def cuts70587 : List PrefixCut := [⟨64,171543199,171543297⟩]
theorem checked70587 : checkPrefixCuts (2^48) 9255911425 10 Manual.Count131072.C070587.packed 64 cuts70587 = true := by
 decide +kernel
def cuts70588 : List PrefixCut := [⟨39,105947472,105947529⟩,
⟨64,174855417,174855510⟩]
theorem checked70588 : checkPrefixCuts (2^48) 9256042497 10 Manual.Count131072.C070588.packed 64 cuts70588 = true := by
 decide +kernel
def pointBounds70588 : List (Nat × Nat × Nat) := [(9256122368,115916421148208,115916810713823)]
theorem point_links_checked70588 : (cuts70588.take 1).map (fun c => (9256042497-1+2*2^10*c.k,115916315200736+c.lower,115916704766294+c.upper)) = pointBounds70588 := by
 decide +kernel
def cuts70589 : List PrefixCut := [⟨64,172754709,172754804⟩]
theorem checked70589 : checkPrefixCuts (2^48) 9256173569 10 Manual.Count131072.C070589.packed 64 cuts70589 = true := by
 decide +kernel
def cuts70590 : List PrefixCut := [⟨53,145566986,145567072⟩,
⟨64,175032919,175033021⟩]
theorem checked70590 : checkPrefixCuts (2^48) 9256304641 10 Manual.Count131072.C070590.packed 64 cuts70590 = true := by
 decide +kernel
def pointBounds70590 : List (Nat × Nat × Nat) := [(9256413184,115916808377848,115917197943680)]
theorem point_links_checked70590 : (cuts70590.take 1).map (fun c => (9256304641-1+2*2^10*c.k,115916662810862+c.lower,115917052376608+c.upper)) = pointBounds70590 := by
 decide +kernel
def cuts70591 : List PrefixCut := [⟨64,171594284,171594392⟩]
theorem checked70591 : checkPrefixCuts (2^48) 9256435713 10 Manual.Count131072.C070591.packed 64 cuts70591 = true := by
 decide +kernel
def cuts70592 : List PrefixCut := [⟨64,172473694,172473797⟩]
theorem checked70592 : checkPrefixCuts (2^48) 9256566785 10 Manual.Count131072.C070592.packed 64 cuts70592 = true := by
 decide +kernel
def cuts70593 : List PrefixCut := [⟨3,8574969,8574973⟩,
⟨64,173839607,173839708⟩]
theorem checked70593 : checkPrefixCuts (2^48) 9256697857 10 Manual.Count131072.C070593.packed 64 cuts70593 = true := by
 decide +kernel
def pointBounds70593 : List (Nat × Nat × Nat) := [(9256704000,115917190486728,115917580052791)]
theorem point_links_checked70593 : (cuts70593.take 1).map (fun c => (9256697857-1+2*2^10*c.k,115917181911759+c.lower,115917571477818+c.upper)) = pointBounds70593 := by
 decide +kernel
def cuts70594 : List PrefixCut := [⟨64,172955315,172955425⟩]
theorem checked70594 : checkPrefixCuts (2^48) 9256828929 10 Manual.Count131072.C070594.packed 64 cuts70594 = true := by
 decide +kernel
def cuts70595 : List PrefixCut := [⟨17,46279121,46279150⟩,
⟨64,174381984,174382092⟩]
theorem checked70595 : checkPrefixCuts (2^48) 9256960001 10 Manual.Count131072.C070595.packed 64 cuts70595 = true := by
 decide +kernel
def pointBounds70595 : List (Nat × Nat × Nat) := [(9256994816,115917574985802,115917964552101)]
theorem point_links_checked70595 : (cuts70595.take 1).map (fun c => (9256960001-1+2*2^10*c.k,115917528706681+c.lower,115917918272951+c.upper)) = pointBounds70595 := by
 decide +kernel
def cuts70596 : List PrefixCut := [⟨64,172342310,172342412⟩]
theorem checked70596 : checkPrefixCuts (2^48) 9257091073 10 Manual.Count131072.C070596.packed 64 cuts70596 = true := by
 decide +kernel
def cuts70597 : List PrefixCut := [⟨31,84102648,84102699⟩,
⟨64,173373662,173373768⟩]
theorem checked70597 : checkPrefixCuts (2^48) 9257222145 10 Manual.Count131072.C070597.packed 64 cuts70597 = true := by
 decide +kernel
def pointBounds70597 : List (Nat × Nat × Nat) := [(9257285632,115917959533623,115918349100154)]
theorem point_links_checked70597 : (cuts70597.take 1).map (fun c => (9257222145-1+2*2^10*c.k,115917875430975+c.lower,115918264997455+c.upper)) = pointBounds70597 := by
 decide +kernel
def cuts70598 : List PrefixCut := [⟨64,175073908,175074007⟩]
theorem checked70598 : checkPrefixCuts (2^48) 9257353217 10 Manual.Count131072.C070598.packed 64 cuts70598 = true := by
 decide +kernel
def cuts70599 : List PrefixCut := [⟨45,121285404,121285479⟩,
⟨64,174493718,174493823⟩]
theorem checked70599 : checkPrefixCuts (2^48) 9257484289 10 Manual.Count131072.C070599.packed 64 cuts70599 = true := by
 decide +kernel
def pointBounds70599 : List (Nat × Nat × Nat) := [(9257576448,115918345163949,115918734730709)]
theorem point_links_checked70599 : (cuts70599.take 1).map (fun c => (9257484289-1+2*2^10*c.k,115918223878545+c.lower,115918613445230+c.upper)) = pointBounds70599 := by
 decide +kernel
def cuts70600 : List PrefixCut := [⟨64,172727807,172727913⟩]
theorem checked70600 : checkPrefixCuts (2^48) 9257615361 10 Manual.Count131072.C070600.packed 64 cuts70600 = true := by
 decide +kernel
def cuts70601 : List PrefixCut := [⟨59,159712521,159712620⟩,
⟨64,173789500,173789607⟩]
theorem checked70601 : checkPrefixCuts (2^48) 9257746433 10 Manual.Count131072.C070601.packed 64 cuts70601 = true := by
 decide +kernel
def pointBounds70601 : List (Nat × Nat × Nat) := [(9257867264,115918730812591,115919120379586)]
theorem point_links_checked70601 : (cuts70601.take 1).map (fun c => (9257746433-1+2*2^10*c.k,115918571100070+c.lower,115918960666966+c.upper)) = pointBounds70601 := by
 decide +kernel
def cuts70602 : List PrefixCut := [⟨64,172692489,172692591⟩]
theorem checked70602 : checkPrefixCuts (2^48) 9257877505 10 Manual.Count131072.C070602.packed 64 cuts70602 = true := by
 decide +kernel
def cuts70603 : List PrefixCut := [⟨64,173206911,173207011⟩]
theorem checked70603 : checkPrefixCuts (2^48) 9258008577 10 Manual.Count131072.C070603.packed 64 cuts70603 = true := by
 decide +kernel
def cuts70604 : List PrefixCut := [⟨9,24474362,24474377⟩,
⟨64,172870026,172870129⟩]
theorem checked70604 : checkPrefixCuts (2^48) 9258139649 10 Manual.Count131072.C070604.packed 64 cuts70604 = true := by
 decide +kernel
def pointBounds70604 : List (Nat × Nat × Nat) := [(9258158080,115919115263332,115919504830552)]
theorem point_links_checked70604 : (cuts70604.take 1).map (fun c => (9258139649-1+2*2^10*c.k,115919090788970+c.lower,115919480356175+c.upper)) = pointBounds70604 := by
 decide +kernel
def cuts70605 : List PrefixCut := [⟨64,173901251,173901362⟩]
theorem checked70605 : checkPrefixCuts (2^48) 9258270721 10 Manual.Count131072.C070605.packed 64 cuts70605 = true := by
 decide +kernel
def cuts70606 : List PrefixCut := [⟨23,62780185,62780222⟩,
⟨64,172165905,172166009⟩]
theorem checked70606 : checkPrefixCuts (2^48) 9258401793 10 Manual.Count131072.C070606.packed 64 cuts70606 = true := by
 decide +kernel
def pointBounds70606 : List (Nat × Nat × Nat) := [(9258448896,115919500340432,115919889907888)]
theorem point_links_checked70606 : (cuts70606.take 1).map (fun c => (9258401793-1+2*2^10*c.k,115919437560247+c.lower,115919827127666+c.upper)) = pointBounds70606 := by
 decide +kernel
def cuts70607 : List PrefixCut := [⟨64,171889846,171889949⟩]
theorem checked70607 : checkPrefixCuts (2^48) 9258532865 10 Manual.Count131072.C070607.packed 64 cuts70607 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000018
