import PlattAssemblyKernel
import PlattCertificates.Count131072.C052592
import PlattCertificates.Count131072.C052593
import PlattCertificates.Count131072.C052594
import PlattCertificates.Count131072.C052595
import PlattCertificates.Count131072.C052596
import PlattCertificates.Count131072.C052597
import PlattCertificates.Count131072.C052598
import PlattCertificates.Count131072.C052599
import PlattCertificates.Count131072.C052600
import PlattCertificates.Count131072.C052601
import PlattCertificates.Count131072.C052602
import PlattCertificates.Count131072.C052603
import PlattCertificates.Count131072.C052604
import PlattCertificates.Count131072.C052605
import PlattCertificates.Count131072.C052606
import PlattCertificates.Count131072.C052607
import PlattCertificates.Count131072.C052608
import PlattCertificates.Count131072.C052609
import PlattCertificates.Count131072.C052610
import PlattCertificates.Count131072.C052611
import PlattCertificates.Count131072.C052612
import PlattCertificates.Count131072.C052613
import PlattCertificates.Count131072.C052614
import PlattCertificates.Count131072.C052615
import PlattCertificates.Count131072.C052616
import PlattCertificates.Count131072.C052617
import PlattCertificates.Count131072.C052618
import PlattCertificates.Count131072.C052619
import PlattCertificates.Count131072.C052620
import PlattCertificates.Count131072.C052621
import PlattCertificates.Count131072.C052622
import PlattCertificates.Count131072.C052623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52592 : List PrefixCut := [⟨64,235673248,235673379⟩]
theorem checked52592 : checkPrefixCuts (2^48) 6897270785 10 Manual.Count131072.C052592.packed 64 cuts52592 = true := by
 decide +kernel
def cuts52593 : List PrefixCut := [⟨16,58927811,58927844⟩,
⟨64,239178286,239178418⟩]
theorem checked52593 : checkPrefixCuts (2^48) 6897401857 10 Manual.Count131072.C052593.packed 64 cuts52593 = true := by
 decide +kernel
def pointBounds52593 : List (Nat × Nat × Nat) := [(6897434624,112285418989939,112285806469410)]
theorem point_links_checked52593 : (cuts52593.take 1).map (fun c => (6897401857-1+2*2^10*c.k,112285360062128+c.lower,112285747541566+c.upper)) = pointBounds52593 := by
 decide +kernel
def cuts52594 : List PrefixCut := [⟨58,215505489,215505613⟩,
⟨64,238439200,238439336⟩]
theorem checked52594 : checkPrefixCuts (2^48) 6897532929 10 Manual.Count131072.C052594.packed 64 cuts52594 = true := by
 decide +kernel
def pointBounds52594 : List (Nat × Nat × Nat) := [(6897651712,112285814745903,112286202225597)]
theorem point_links_checked52594 : (cuts52594.take 1).map (fun c => (6897532929-1+2*2^10*c.k,112285599240414+c.lower,112285986719984+c.upper)) = pointBounds52594 := by
 decide +kernel
def cuts52595 : List PrefixCut := [⟨64,237577702,237577834⟩]
theorem checked52595 : checkPrefixCuts (2^48) 6897664001 10 Manual.Count131072.C052595.packed 64 cuts52595 = true := by
 decide +kernel
def cuts52596 : List PrefixCut := [⟨36,130212852,130212926⟩,
⟨64,234961597,234961727⟩]
theorem checked52596 : checkPrefixCuts (2^48) 6897795073 10 Manual.Count131072.C052596.packed 64 cuts52596 = true := by
 decide +kernel
def pointBounds52596 : List (Nat × Nat × Nat) := [(6897868800,112286205470168,112286592950080)]
theorem point_links_checked52596 : (cuts52596.take 1).map (fun c => (6897795073-1+2*2^10*c.k,112286075257316+c.lower,112286462737154+c.upper)) = pointBounds52596 := by
 decide +kernel
def cuts52597 : List PrefixCut := [⟨64,238588850,238588983⟩]
theorem checked52597 : checkPrefixCuts (2^48) 6897926145 10 Manual.Count131072.C052597.packed 64 cuts52597 = true := by
 decide +kernel
def cuts52598 : List PrefixCut := [⟨14,51862985,51863013⟩,
⟨64,235850390,235850518⟩]
theorem checked52598 : checkPrefixCuts (2^48) 6898057217 10 Manual.Count131072.C052598.packed 64 cuts52598 = true := by
 decide +kernel
def pointBounds52598 : List (Nat × Nat × Nat) := [(6898085888,112286600670748,112286988150877)]
theorem point_links_checked52598 : (cuts52598.take 1).map (fun c => (6898057217-1+2*2^10*c.k,112286548807763+c.lower,112286936287864+c.upper)) = pointBounds52598 := by
 decide +kernel
def cuts52599 : List PrefixCut := [⟨56,207038675,207038791⟩,
⟨64,235152253,235152385⟩]
theorem checked52599 : checkPrefixCuts (2^48) 6898188289 10 Manual.Count131072.C052599.packed 64 cuts52599 = true := by
 decide +kernel
def pointBounds52599 : List (Nat × Nat × Nat) := [(6898302976,112286991696828,112287379177173)]
theorem point_links_checked52599 : (cuts52599.take 1).map (fun c => (6898188289-1+2*2^10*c.k,112286784658153+c.lower,112287172138382+c.upper)) = pointBounds52599 := by
 decide +kernel
def cuts52600 : List PrefixCut := [⟨64,235066165,235066301⟩]
theorem checked52600 : checkPrefixCuts (2^48) 6898319361 10 Manual.Count131072.C052600.packed 64 cuts52600 = true := by
 decide +kernel
def cuts52601 : List PrefixCut := [⟨34,125875479,125875547⟩,
⟨64,235714546,235714678⟩]
theorem checked52601 : checkPrefixCuts (2^48) 6898450433 10 Manual.Count131072.C052601.packed 64 cuts52601 = true := by
 decide +kernel
def pointBounds52601 : List (Nat × Nat × Nat) := [(6898520064,112287380752050,112287768232615)]
theorem point_links_checked52601 : (cuts52601.take 1).map (fun c => (6898450433-1+2*2^10*c.k,112287254876571+c.lower,112287642357068+c.upper)) = pointBounds52601 := by
 decide +kernel
def cuts52602 : List PrefixCut := [⟨64,236607708,236607842⟩]
theorem checked52602 : checkPrefixCuts (2^48) 6898581505 10 Manual.Count131072.C052602.packed 64 cuts52602 = true := by
 decide +kernel
def cuts52603 : List PrefixCut := [⟨12,42963455,42963481⟩,
⟨64,234603960,234604093⟩]
theorem checked52603 : checkPrefixCuts (2^48) 6898712577 10 Manual.Count131072.C052603.packed 64 cuts52603 = true := by
 decide +kernel
def pointBounds52603 : List (Nat × Nat × Nat) := [(6898737152,112287770162280,112288157643069)]
theorem point_links_checked52603 : (cuts52603.take 1).map (fun c => (6898712577-1+2*2^10*c.k,112287727198825+c.lower,112288114679588+c.upper)) = pointBounds52603 := by
 decide +kernel
def cuts52604 : List PrefixCut := [⟨54,199348675,199348788⟩,
⟨64,236068303,236068436⟩]
theorem checked52604 : checkPrefixCuts (2^48) 6898843649 10 Manual.Count131072.C052604.packed 64 cuts52604 = true := by
 decide +kernel
def pointBounds52604 : List (Nat × Nat × Nat) := [(6898954240,112288161151460,112288548632469)]
theorem point_links_checked52604 : (cuts52604.take 1).map (fun c => (6898843649-1+2*2^10*c.k,112287961802785+c.lower,112288349283681+c.upper)) = pointBounds52604 := by
 decide +kernel
def cuts52605 : List PrefixCut := [⟨64,236798209,236798346⟩]
theorem checked52605 : checkPrefixCuts (2^48) 6898974721 10 Manual.Count131072.C052605.packed 64 cuts52605 = true := by
 decide +kernel
def cuts52606 : List PrefixCut := [⟨32,118438211,118438278⟩,
⟨64,237446468,237446604⟩]
theorem checked52606 : checkPrefixCuts (2^48) 6899105793 10 Manual.Count131072.C052606.packed 64 cuts52606 = true := by
 decide +kernel
def pointBounds52606 : List (Nat × Nat × Nat) := [(6899171328,112288553107508,112288940588741)]
theorem point_links_checked52606 : (cuts52606.take 1).map (fun c => (6899105793-1+2*2^10*c.k,112288434669297+c.lower,112288822150463+c.upper)) = pointBounds52606 := by
 decide +kernel
def cuts52607 : List PrefixCut := [⟨64,237156376,237156511⟩]
theorem checked52607 : checkPrefixCuts (2^48) 6899236865 10 Manual.Count131072.C052607.packed 64 cuts52607 = true := by
 decide +kernel
def cuts52608 : List PrefixCut := [⟨10,37288586,37288607⟩,
⟨64,235234445,235234578⟩]
theorem checked52608 : checkPrefixCuts (2^48) 6899367937 10 Manual.Count131072.C052608.packed 64 cuts52608 = true := by
 decide +kernel
def pointBounds52608 : List (Nat × Nat × Nat) := [(6899388416,112288946560727,112289334042185)]
theorem point_links_checked52608 : (cuts52608.take 1).map (fun c => (6899367937-1+2*2^10*c.k,112288909272141+c.lower,112289296753578+c.upper)) = pointBounds52608 := by
 decide +kernel
def cuts52609 : List PrefixCut := [⟨52,196310887,196310999⟩,
⟨64,240737430,240737566⟩]
theorem checked52609 : checkPrefixCuts (2^48) 6899499009 10 Manual.Count131072.C052609.packed 64 cuts52609 = true := by
 decide +kernel
def pointBounds52609 : List (Nat × Nat × Nat) := [(6899605504,112289340817473,112289728299155)]
theorem point_links_checked52609 : (cuts52609.take 1).map (fun c => (6899499009-1+2*2^10*c.k,112289144506586+c.lower,112289531988156+c.upper)) = pointBounds52609 := by
 decide +kernel
def cuts52610 : List PrefixCut := [⟨64,238203549,238203682⟩]
theorem checked52610 : checkPrefixCuts (2^48) 6899630081 10 Manual.Count131072.C052610.packed 64 cuts52610 = true := by
 decide +kernel
def cuts52611 : List PrefixCut := [⟨30,110268060,110268121⟩,
⟨64,236567239,236567368⟩]
theorem checked52611 : checkPrefixCuts (2^48) 6899761153 10 Manual.Count131072.C052611.packed 64 cuts52611 = true := by
 decide +kernel
def pointBounds52611 : List (Nat × Nat × Nat) := [(6899822592,112289733715625,112290121197525)]
theorem point_links_checked52611 : (cuts52611.take 1).map (fun c => (6899761153-1+2*2^10*c.k,112289623447565+c.lower,112290010929404+c.upper)) = pointBounds52611 := by
 decide +kernel
def cuts52612 : List PrefixCut := [⟨64,234931005,234931137⟩]
theorem checked52612 : checkPrefixCuts (2^48) 6899892225 10 Manual.Count131072.C052612.packed 64 cuts52612 = true := by
 decide +kernel
def cuts52613 : List PrefixCut := [⟨8,29615919,29615935⟩,
⟨64,234396231,234396366⟩]
theorem checked52613 : checkPrefixCuts (2^48) 6900023297 10 Manual.Count131072.C052613.packed 64 cuts52613 = true := by
 decide +kernel
def pointBounds52613 : List (Nat × Nat × Nat) := [(6900039680,112290124561728,112290512043844)]
theorem point_links_checked52613 : (cuts52613.take 1).map (fun c => (6900023297-1+2*2^10*c.k,112290094945809+c.lower,112290482427909+c.upper)) = pointBounds52613 := by
 decide +kernel
def cuts52614 : List PrefixCut := [⟨50,185971857,185971958⟩,
⟨64,238144648,238144780⟩]
theorem checked52614 : checkPrefixCuts (2^48) 6900154369 10 Manual.Count131072.C052614.packed 64 cuts52614 = true := by
 decide +kernel
def pointBounds52614 : List (Nat × Nat × Nat) := [(6900256768,112290515313897,112290902796233)]
theorem point_links_checked52614 : (cuts52614.take 1).map (fun c => (6900154369-1+2*2^10*c.k,112290329342040+c.lower,112290716824275+c.upper)) = pointBounds52614 := by
 decide +kernel
def cuts52615 : List PrefixCut := [⟨64,233571493,233571628⟩]
theorem checked52615 : checkPrefixCuts (2^48) 6900285441 10 Manual.Count131072.C052615.packed 64 cuts52615 = true := by
 decide +kernel
def cuts52616 : List PrefixCut := [⟨28,102099450,102099507⟩,
⟨64,234586808,234586941⟩]
theorem checked52616 : checkPrefixCuts (2^48) 6900416513 10 Manual.Count131072.C052616.packed 64 cuts52616 = true := by
 decide +kernel
def pointBounds52616 : List (Nat × Nat × Nat) := [(6900473856,112290903157631,112291290640190)]
theorem point_links_checked52616 : (cuts52616.take 1).map (fun c => (6900416513-1+2*2^10*c.k,112290801058181+c.lower,112291188540683+c.upper)) = pointBounds52616 := by
 decide +kernel
def cuts52617 : List PrefixCut := [⟨64,231808662,231808794⟩]
theorem checked52617 : checkPrefixCuts (2^48) 6900547585 10 Manual.Count131072.C052617.packed 64 cuts52617 = true := by
 decide +kernel
def cuts52618 : List PrefixCut := [⟨6,22352600,22352613⟩,
⟨64,236984460,236984592⟩]
theorem checked52618 : checkPrefixCuts (2^48) 6900678657 10 Manual.Count131072.C052618.packed 64 cuts52618 = true := by
 decide +kernel
def pointBounds52618 : List (Nat × Nat × Nat) := [(6900690944,112291289806251,112291677289031)]
theorem point_links_checked52618 : (cuts52618.take 1).map (fun c => (6900678657-1+2*2^10*c.k,112291267453651+c.lower,112291654936418+c.upper)) = pointBounds52618 := by
 decide +kernel
def cuts52619 : List PrefixCut := [⟨48,173840111,173840210⟩,
⟨64,232534040,232534172⟩]
theorem checked52619 : checkPrefixCuts (2^48) 6900809729 10 Manual.Count131072.C052619.packed 64 cuts52619 = true := by
 decide +kernel
def pointBounds52619 : List (Nat × Nat × Nat) := [(6900908032,112291678278222,112292065761220)]
theorem point_links_checked52619 : (cuts52619.take 1).map (fun c => (6900809729-1+2*2^10*c.k,112291504438111+c.lower,112291891921010+c.upper)) = pointBounds52619 := by
 decide +kernel
def cuts52620 : List PrefixCut := [⟨64,231795431,231795567⟩]
theorem checked52620 : checkPrefixCuts (2^48) 6900940801 10 Manual.Count131072.C052620.packed 64 cuts52620 = true := by
 decide +kernel
def cuts52621 : List PrefixCut := [⟨26,95237581,95237634⟩,
⟨64,235869723,235869855⟩]
theorem checked52621 : checkPrefixCuts (2^48) 6901071873 10 Manual.Count131072.C052621.packed 64 cuts52621 = true := by
 decide +kernel
def pointBounds52621 : List (Nat × Nat × Nat) := [(6901125120,112292064005163,112292451488383)]
theorem point_links_checked52621 : (cuts52621.take 1).map (fun c => (6901071873-1+2*2^10*c.k,112291968767582+c.lower,112292356250749+c.upper)) = pointBounds52621 := by
 decide +kernel
def cuts52622 : List PrefixCut := [⟨64,239535971,239536107⟩]
theorem checked52622 : checkPrefixCuts (2^48) 6901202945 10 Manual.Count131072.C052622.packed 64 cuts52622 = true := by
 decide +kernel
def cuts52623 : List PrefixCut := [⟨4,15253797,15253805⟩,
⟨64,236798817,236798952⟩]
theorem checked52623 : checkPrefixCuts (2^48) 6901334017 10 Manual.Count131072.C052623.packed 64 cuts52623 = true := by
 decide +kernel
def pointBounds52623 : List (Nat × Nat × Nat) := [(6901342208,112292459427073,112292846910516)]
theorem point_links_checked52623 : (cuts52623.take 1).map (fun c => (6901334017-1+2*2^10*c.k,112292444173276+c.lower,112292831656711+c.upper)) = pointBounds52623 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000081
