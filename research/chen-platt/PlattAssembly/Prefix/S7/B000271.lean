import PlattAssemblyKernel
import PlattCertificates.Count131072.C068672
import PlattCertificates.Count131072.C068673
import PlattCertificates.Count131072.C068674
import PlattCertificates.Count131072.C068675
import PlattCertificates.Count131072.C068676
import PlattCertificates.Count131072.C068677
import PlattCertificates.Count131072.C068678
import PlattCertificates.Count131072.C068679
import PlattCertificates.Count131072.C068680
import PlattCertificates.Count131072.C068681
import PlattCertificates.Count131072.C068682
import PlattCertificates.Count131072.C068683
import PlattCertificates.Count131072.C068684
import PlattCertificates.Count131072.C068685
import PlattCertificates.Count131072.C068686
import PlattCertificates.Count131072.C068687
import PlattCertificates.Count131072.C068688
import PlattCertificates.Count131072.C068689
import PlattCertificates.Count131072.C068690
import PlattCertificates.Count131072.C068691
import PlattCertificates.Count131072.C068692
import PlattCertificates.Count131072.C068693
import PlattCertificates.Count131072.C068694
import PlattCertificates.Count131072.C068695
import PlattCertificates.Count131072.C068696
import PlattCertificates.Count131072.C068697
import PlattCertificates.Count131072.C068698
import PlattCertificates.Count131072.C068699
import PlattCertificates.Count131072.C068700
import PlattCertificates.Count131072.C068701
import PlattCertificates.Count131072.C068702
import PlattCertificates.Count131072.C068703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000271
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68672 : List PrefixCut := [⟨57,155444731,155444825⟩,
⟨64,175730856,175730962⟩]
theorem checked68672 : checkPrefixCuts (2^48) 9004908545 10 Manual.Count131072.C068672.packed 64 cuts68672 = true := by
 decide +kernel
def pointBounds68672 : List (Nat × Nat × Nat) := [(9005025280,115578892448885,115579281816162)]
theorem point_links_checked68672 : (cuts68672.take 1).map (fun c => (9004908545-1+2*2^10*c.k,115578737004154+c.lower,115579126371337+c.upper)) = pointBounds68672 := by
 decide +kernel
def cuts68673 : List PrefixCut := [⟨64,180291861,180291968⟩]
theorem checked68673 : checkPrefixCuts (2^48) 9005039617 10 Manual.Count131072.C068673.packed 64 cuts68673 = true := by
 decide +kernel
def cuts68674 : List PrefixCut := [⟨64,178226278,178226383⟩]
theorem checked68674 : checkPrefixCuts (2^48) 9005170689 10 Manual.Count131072.C068674.packed 64 cuts68674 = true := by
 decide +kernel
def cuts68675 : List PrefixCut := [⟨3,8157963,8157969⟩,
⟨64,179598980,179599084⟩]
theorem checked68675 : checkPrefixCuts (2^48) 9005301761 10 Manual.Count131072.C068675.packed 64 cuts68675 = true := by
 decide +kernel
def pointBounds68675 : List (Nat × Nat × Nat) := [(9005307904,115579279411112,115579668778619)]
theorem point_links_checked68675 : (cuts68675.take 1).map (fun c => (9005301761-1+2*2^10*c.k,115579271253149+c.lower,115579660620650+c.upper)) = pointBounds68675 := by
 decide +kernel
def cuts68676 : List PrefixCut := [⟨64,180252733,180252835⟩]
theorem checked68676 : checkPrefixCuts (2^48) 9005432833 10 Manual.Count131072.C068676.packed 64 cuts68676 = true := by
 decide +kernel
def cuts68677 : List PrefixCut := [⟨13,36256519,36256540⟩,
⟨64,179656255,179656359⟩]
theorem checked68677 : checkPrefixCuts (2^48) 9005563905 10 Manual.Count131072.C068677.packed 64 cuts68677 = true := by
 decide +kernel
def pointBounds68677 : List (Nat × Nat × Nat) := [(9005590528,115579667361381,115580056729109)]
theorem point_links_checked68677 : (cuts68677.take 1).map (fun c => (9005563905-1+2*2^10*c.k,115579631104862+c.lower,115580020472569+c.upper)) = pointBounds68677 := by
 decide +kernel
def cuts68678 : List PrefixCut := [⟨64,179216075,179216184⟩]
theorem checked68678 : checkPrefixCuts (2^48) 9005694977 10 Manual.Count131072.C068678.packed 64 cuts68678 = true := by
 decide +kernel
def cuts68679 : List PrefixCut := [⟨23,61946765,61946801⟩,
⟨64,175806718,175806822⟩]
theorem checked68679 : checkPrefixCuts (2^48) 9005826049 10 Manual.Count131072.C068679.packed 64 cuts68679 = true := by
 decide +kernel
def pointBounds68679 : List (Nat × Nat × Nat) := [(9005873152,115580051923957,115580441291913)]
theorem point_links_checked68679 : (cuts68679.take 1).map (fun c => (9005826049-1+2*2^10*c.k,115579989977192+c.lower,115580379345112+c.upper)) = pointBounds68679 := by
 decide +kernel
def cuts68680 : List PrefixCut := [⟨64,178023208,178023310⟩]
theorem checked68680 : checkPrefixCuts (2^48) 9005957121 10 Manual.Count131072.C068680.packed 64 cuts68680 = true := by
 decide +kernel
def cuts68681 : List PrefixCut := [⟨33,93479899,93479955⟩,
⟨64,179739560,179739665⟩]
theorem checked68681 : checkPrefixCuts (2^48) 9006088193 10 Manual.Count131072.C068681.packed 64 cuts68681 = true := by
 decide +kernel
def pointBounds68681 : List (Nat × Nat × Nat) := [(9006155776,115580437287017,115580826655199)]
theorem point_links_checked68681 : (cuts68681.take 1).map (fun c => (9006088193-1+2*2^10*c.k,115580343807118+c.lower,115580733175244+c.upper)) = pointBounds68681 := by
 decide +kernel
def cuts68682 : List PrefixCut := [⟨64,180143242,180143345⟩]
theorem checked68682 : checkPrefixCuts (2^48) 9006219265 10 Manual.Count131072.C068682.packed 64 cuts68682 = true := by
 decide +kernel
def cuts68683 : List PrefixCut := [⟨43,120573243,120573306⟩,
⟨64,178984272,178984368⟩]
theorem checked68683 : checkPrefixCuts (2^48) 9006350337 10 Manual.Count131072.C068683.packed 64 cuts68683 = true := by
 decide +kernel
def pointBounds68683 : List (Nat × Nat × Nat) := [(9006438400,115580824263163,115581213631560)]
theorem point_links_checked68683 : (cuts68683.take 1).map (fun c => (9006350337-1+2*2^10*c.k,115580703689920+c.lower,115581093058254+c.upper)) = pointBounds68683 := by
 decide +kernel
def cuts68684 : List PrefixCut := [⟨64,180919302,180919411⟩]
theorem checked68684 : checkPrefixCuts (2^48) 9006481409 10 Manual.Count131072.C068684.packed 64 cuts68684 = true := by
 decide +kernel
def cuts68685 : List PrefixCut := [⟨53,147008649,147008738⟩,
⟨64,178260260,178260367⟩]
theorem checked68685 : checkPrefixCuts (2^48) 9006612481 10 Manual.Count131072.C068685.packed 64 cuts68685 = true := by
 decide +kernel
def pointBounds68685 : List (Nat × Nat × Nat) := [(9006721024,115581210602143,115581599970771)]
theorem point_links_checked68685 : (cuts68685.take 1).map (fun c => (9006612481-1+2*2^10*c.k,115581063593494+c.lower,115581452962033+c.upper)) = pointBounds68685 := by
 decide +kernel
def cuts68686 : List PrefixCut := [⟨64,176882604,176882710⟩]
theorem checked68686 : checkPrefixCuts (2^48) 9006743553 10 Manual.Count131072.C068686.packed 64 cuts68686 = true := by
 decide +kernel
def cuts68687 : List PrefixCut := [⟨63,177692566,177692672⟩,
⟨64,180661379,180661487⟩]
theorem checked68687 : checkPrefixCuts (2^48) 9006874625 10 Manual.Count131072.C068687.packed 64 cuts68687 = true := by
 decide +kernel
def pointBounds68687 : List (Nat × Nat × Nat) := [(9007003648,115581596428924,115581985797782)]
theorem point_links_checked68687 : (cuts68687.take 1).map (fun c => (9006874625-1+2*2^10*c.k,115581418736358+c.lower,115581808105110+c.upper)) = pointBounds68687 := by
 decide +kernel
def cuts68688 : List PrefixCut := [⟨64,177564969,177565072⟩]
theorem checked68688 : checkPrefixCuts (2^48) 9007005697 10 Manual.Count131072.C068688.packed 64 cuts68688 = true := by
 decide +kernel
def cuts68689 : List PrefixCut := [⟨64,180124899,180125003⟩]
theorem checked68689 : checkPrefixCuts (2^48) 9007136769 10 Manual.Count131072.C068689.packed 64 cuts68689 = true := by
 decide +kernel
def cuts68690 : List PrefixCut := [⟨9,24687279,24687296⟩,
⟨64,177716054,177716165⟩]
theorem checked68690 : checkPrefixCuts (2^48) 9007267841 10 Manual.Count131072.C068690.packed 64 cuts68690 = true := by
 decide +kernel
def pointBounds68690 : List (Nat × Nat × Nat) := [(9007286272,115581981774884,115582371143968)]
theorem point_links_checked68690 : (cuts68690.take 1).map (fun c => (9007267841-1+2*2^10*c.k,115581957087605+c.lower,115582346456672+c.upper)) = pointBounds68690 := by
 decide +kernel
def cuts68691 : List PrefixCut := [⟨64,176244749,176244854⟩]
theorem checked68691 : checkPrefixCuts (2^48) 9007398913 10 Manual.Count131072.C068691.packed 64 cuts68691 = true := by
 decide +kernel
def cuts68692 : List PrefixCut := [⟨19,54591611,54591639⟩,
⟨64,180929490,180929594⟩]
theorem checked68692 : checkPrefixCuts (2^48) 9007529985 10 Manual.Count131072.C068692.packed 64 cuts68692 = true := by
 decide +kernel
def pointBounds68692 : List (Nat × Nat × Nat) := [(9007568896,115582365640019,115582755009330)]
theorem point_links_checked68692 : (cuts68692.take 1).map (fun c => (9007529985-1+2*2^10*c.k,115582311048408+c.lower,115582700417691+c.upper)) = pointBounds68692 := by
 decide +kernel
def cuts68693 : List PrefixCut := [⟨64,180458137,180458237⟩]
theorem checked68693 : checkPrefixCuts (2^48) 9007661057 10 Manual.Count131072.C068693.packed 64 cuts68693 = true := by
 decide +kernel
def cuts68694 : List PrefixCut := [⟨29,80244429,80244477⟩,
⟨64,176049576,176049681⟩]
theorem checked68694 : checkPrefixCuts (2^48) 9007792129 10 Manual.Count131072.C068694.packed 64 cuts68694 = true := by
 decide +kernel
def pointBounds68694 : List (Nat × Nat × Nat) := [(9007851520,115582752680464,115583142049999)]
theorem point_links_checked68694 : (cuts68694.take 1).map (fun c => (9007792129-1+2*2^10*c.k,115582672436035+c.lower,115583061805522+c.upper)) = pointBounds68694 := by
 decide +kernel
def cuts68695 : List PrefixCut := [⟨64,179577963,179578062⟩]
theorem checked68695 : checkPrefixCuts (2^48) 9007923201 10 Manual.Count131072.C068695.packed 64 cuts68695 = true := by
 decide +kernel
def cuts68696 : List PrefixCut := [⟨39,109614072,109614137⟩,
⟨64,179919054,179919160⟩]
theorem checked68696 : checkPrefixCuts (2^48) 9008054273 10 Manual.Count131072.C068696.packed 64 cuts68696 = true := by
 decide +kernel
def pointBounds68696 : List (Nat × Nat × Nat) := [(9008134144,115583137677646,115583527047402)]
theorem point_links_checked68696 : (cuts68696.take 1).map (fun c => (9008054273-1+2*2^10*c.k,115583028063574+c.lower,115583417433265+c.upper)) = pointBounds68696 := by
 decide +kernel
def cuts68697 : List PrefixCut := [⟨64,179572710,179572820⟩]
theorem checked68697 : checkPrefixCuts (2^48) 9008185345 10 Manual.Count131072.C068697.packed 64 cuts68697 = true := by
 decide +kernel
def cuts68698 : List PrefixCut := [⟨49,136544761,136544842⟩,
⟨64,178476509,178476615⟩]
theorem checked68698 : checkPrefixCuts (2^48) 9008316417 10 Manual.Count131072.C068698.packed 64 cuts68698 = true := by
 decide +kernel
def pointBounds68698 : List (Nat × Nat × Nat) := [(9008416768,115583524100099,115583913470087)]
theorem point_links_checked68698 : (cuts68698.take 1).map (fun c => (9008316417-1+2*2^10*c.k,115583387555338+c.lower,115583776925245+c.upper)) = pointBounds68698 := by
 decide +kernel
def cuts68699 : List PrefixCut := [⟨64,179754984,179755092⟩]
theorem checked68699 : checkPrefixCuts (2^48) 9008447489 10 Manual.Count131072.C068699.packed 64 cuts68699 = true := by
 decide +kernel
def cuts68700 : List PrefixCut := [⟨59,163161370,163161470⟩,
⟨64,177034047,177034156⟩]
theorem checked68700 : checkPrefixCuts (2^48) 9008578561 10 Manual.Count131072.C068700.packed 64 cuts68700 = true := by
 decide +kernel
def pointBounds68700 : List (Nat × Nat × Nat) := [(9008699392,115583908948201,115584298318422)]
theorem point_links_checked68700 : (cuts68700.take 1).map (fun c => (9008578561-1+2*2^10*c.k,115583745786831+c.lower,115584135156952+c.upper)) = pointBounds68700 := by
 decide +kernel
def cuts68701 : List PrefixCut := [⟨64,179999708,179999811⟩]
theorem checked68701 : checkPrefixCuts (2^48) 9008709633 10 Manual.Count131072.C068701.packed 64 cuts68701 = true := by
 decide +kernel
def cuts68702 : List PrefixCut := [⟨64,179997090,179997199⟩]
theorem checked68702 : checkPrefixCuts (2^48) 9008840705 10 Manual.Count131072.C068702.packed 64 cuts68702 = true := by
 decide +kernel
def cuts68703 : List PrefixCut := [⟨5,13809770,13809778⟩,
⟨64,176432692,176432797⟩]
theorem checked68703 : checkPrefixCuts (2^48) 9008971777 10 Manual.Count131072.C068703.packed 64 cuts68703 = true := by
 decide +kernel
def pointBounds68703 : List (Nat × Nat × Nat) := [(9008982016,115584296627446,115584685997896)]
theorem point_links_checked68703 : (cuts68703.take 1).map (fun c => (9008971777-1+2*2^10*c.k,115584282817676+c.lower,115584672188118+c.upper)) = pointBounds68703 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000271
