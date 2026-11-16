import PlattAssemblyKernel
import PlattCertificates.Count131072.C061984
import PlattCertificates.Count131072.C061985
import PlattCertificates.Count131072.C061986
import PlattCertificates.Count131072.C061987
import PlattCertificates.Count131072.C061988
import PlattCertificates.Count131072.C061989
import PlattCertificates.Count131072.C061990
import PlattCertificates.Count131072.C061991
import PlattCertificates.Count131072.C061992
import PlattCertificates.Count131072.C061993
import PlattCertificates.Count131072.C061994
import PlattCertificates.Count131072.C061995
import PlattCertificates.Count131072.C061996
import PlattCertificates.Count131072.C061997
import PlattCertificates.Count131072.C061998
import PlattCertificates.Count131072.C061999
import PlattCertificates.Count131072.C062000
import PlattCertificates.Count131072.C062001
import PlattCertificates.Count131072.C062002
import PlattCertificates.Count131072.C062003
import PlattCertificates.Count131072.C062004
import PlattCertificates.Count131072.C062005
import PlattCertificates.Count131072.C062006
import PlattCertificates.Count131072.C062007
import PlattCertificates.Count131072.C062008
import PlattCertificates.Count131072.C062009
import PlattCertificates.Count131072.C062010
import PlattCertificates.Count131072.C062011
import PlattCertificates.Count131072.C062012
import PlattCertificates.Count131072.C062013
import PlattCertificates.Count131072.C062014
import PlattCertificates.Count131072.C062015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61984 : List PrefixCut := [⟨19,58626761,58626796⟩,
⟨64,200396418,200396540⟩]
theorem checked61984 : checkPrefixCuts (2^48) 8128299009 10 Manual.Count131072.C061984.packed 64 cuts61984 = true := by
 decide +kernel
def pointBounds61984 : List (Nat × Nat × Nat) := [(8128337920,114318258336617,114318646973617)]
theorem point_links_checked61984 : (cuts61984.take 1).map (fun c => (8128299009-1+2*2^10*c.k,114318199709856+c.lower,114318588346821+c.upper)) = pointBounds61984 := by
 decide +kernel
def cuts61985 : List PrefixCut := [⟨64,198696419,198696531⟩]
theorem checked61985 : checkPrefixCuts (2^48) 8128430081 10 Manual.Count131072.C061985.packed 64 cuts61985 = true := by
 decide +kernel
def cuts61986 : List PrefixCut := [⟨16,49621663,49621691⟩,
⟨64,201982818,201982935⟩]
theorem checked61986 : checkPrefixCuts (2^48) 8128561153 10 Manual.Count131072.C061986.packed 64 cuts61986 = true := by
 decide +kernel
def pointBounds61986 : List (Nat × Nat × Nat) := [(8128593920,114318648424356,114319037061583)]
theorem point_links_checked61986 : (cuts61986.take 1).map (fun c => (8128561153-1+2*2^10*c.k,114318598802693+c.lower,114318987439892+c.upper)) = pointBounds61986 := by
 decide +kernel
def cuts61987 : List PrefixCut := [⟨64,199555685,199555804⟩]
theorem checked61987 : checkPrefixCuts (2^48) 8128692225 10 Manual.Count131072.C061987.packed 64 cuts61987 = true := by
 decide +kernel
def cuts61988 : List PrefixCut := [⟨13,41344297,41344319⟩,
⟨64,201491566,201491680⟩]
theorem checked61988 : checkPrefixCuts (2^48) 8128823297 10 Manual.Count131072.C061988.packed 64 cuts61988 = true := by
 decide +kernel
def pointBounds61988 : List (Nat × Nat × Nat) := [(8128849920,114319041685493,114319430322950)]
theorem point_links_checked61988 : (cuts61988.take 1).map (fun c => (8128823297-1+2*2^10*c.k,114319000341196+c.lower,114319388978631+c.upper)) = pointBounds61988 := by
 decide +kernel
def cuts61989 : List PrefixCut := [⟨64,200414903,200415015⟩]
theorem checked61989 : checkPrefixCuts (2^48) 8128954369 10 Manual.Count131072.C061989.packed 64 cuts61989 = true := by
 decide +kernel
def cuts61990 : List PrefixCut := [⟨10,31405430,31405445⟩,
⟨64,197884018,197884131⟩]
theorem checked61990 : checkPrefixCuts (2^48) 8129085441 10 Manual.Count131072.C061990.packed 64 cuts61990 = true := by
 decide +kernel
def pointBounds61990 : List (Nat × Nat × Nat) := [(8129105920,114319433653095,114319822290771)]
theorem point_links_checked61990 : (cuts61990.take 1).map (fun c => (8129085441-1+2*2^10*c.k,114319402247665+c.lower,114319790885326+c.upper)) = pointBounds61990 := by
 decide +kernel
def cuts61991 : List PrefixCut := [⟨64,198504068,198504185⟩]
theorem checked61991 : checkPrefixCuts (2^48) 8129216513 10 Manual.Count131072.C061991.packed 64 cuts61991 = true := by
 decide +kernel
def cuts61992 : List PrefixCut := [⟨7,22298182,22298195⟩,
⟨64,198639362,198639481⟩]
theorem checked61992 : checkPrefixCuts (2^48) 8129347585 10 Manual.Count131072.C061992.packed 64 cuts61992 = true := by
 decide +kernel
def pointBounds61992 : List (Nat × Nat × Nat) := [(8129361920,114319820933933,114320209571837)]
theorem point_links_checked61992 : (cuts61992.take 1).map (fun c => (8129347585-1+2*2^10*c.k,114319798635751+c.lower,114320187273642+c.upper)) = pointBounds61992 := by
 decide +kernel
def cuts61993 : List PrefixCut := [⟨64,198670789,198670897⟩]
theorem checked61993 : checkPrefixCuts (2^48) 8129478657 10 Manual.Count131072.C061993.packed 64 cuts61993 = true := by
 decide +kernel
def cuts61994 : List PrefixCut := [⟨4,11771957,11771964⟩,
⟨64,198321355,198321466⟩]
theorem checked61994 : checkPrefixCuts (2^48) 8129609729 10 Manual.Count131072.C061994.packed 64 cuts61994 = true := by
 decide +kernel
def pointBounds61994 : List (Nat × Nat × Nat) := [(8129617920,114320207717859,114320596355984)]
theorem point_links_checked61994 : (cuts61994.take 1).map (fun c => (8129609729-1+2*2^10*c.k,114320195945902+c.lower,114320584584020+c.upper)) = pointBounds61994 := by
 decide +kernel
def cuts61995 : List PrefixCut := [⟨64,200291652,200291762⟩]
theorem checked61995 : checkPrefixCuts (2^48) 8129740801 10 Manual.Count131072.C061995.packed 64 cuts61995 = true := by
 decide +kernel
def cuts61996 : List PrefixCut := [⟨1,3081385,3081386⟩,
⟨64,198557301,198557416⟩]
theorem checked61996 : checkPrefixCuts (2^48) 8129871873 10 Manual.Count131072.C061996.packed 64 cuts61996 = true := by
 decide +kernel
def pointBounds61996 : List (Nat × Nat × Nat) := [(8129873920,114320597640294,114320986278634)]
theorem point_links_checked61996 : (cuts61996.take 1).map (fun c => (8129871873-1+2*2^10*c.k,114320594558909+c.lower,114320983197248+c.upper)) = pointBounds61996 := by
 decide +kernel
def cuts61997 : List PrefixCut := [⟨62,194468823,194468931⟩,
⟨64,201046850,201046962⟩]
theorem checked61997 : checkPrefixCuts (2^48) 8130002945 10 Manual.Count131072.C061997.packed 64 cuts61997 = true := by
 decide +kernel
def pointBounds61997 : List (Nat × Nat × Nat) := [(8130129920,114320987585033,114321376223595)]
theorem point_links_checked61997 : (cuts61997.take 1).map (fun c => (8130002945-1+2*2^10*c.k,114320793116210+c.lower,114321181754664+c.upper)) = pointBounds61997 := by
 decide +kernel
def cuts61998 : List PrefixCut := [⟨64,199416417,199416529⟩]
theorem checked61998 : checkPrefixCuts (2^48) 8130134017 10 Manual.Count131072.C061998.packed 64 cuts61998 = true := by
 decide +kernel
def cuts61999 : List PrefixCut := [⟨59,183591831,183591940⟩,
⟨64,199067013,199067131⟩]
theorem checked61999 : checkPrefixCuts (2^48) 8130265089 10 Manual.Count131072.C061999.packed 64 cuts61999 = true := by
 decide +kernel
def pointBounds61999 : List (Nat × Nat × Nat) := [(8130385920,114321377171308,114321765810095)]
theorem point_links_checked61999 : (cuts61999.take 1).map (fun c => (8130265089-1+2*2^10*c.k,114321193579477+c.lower,114321582218155+c.upper)) = pointBounds61999 := by
 decide +kernel
def cuts62000 : List PrefixCut := [⟨64,195532579,195532691⟩]
theorem checked62000 : checkPrefixCuts (2^48) 8130396161 10 Manual.Count131072.C062000.packed 64 cuts62000 = true := by
 decide +kernel
def cuts62001 : List PrefixCut := [⟨56,174515747,174515846⟩,
⟨64,198368232,198368345⟩]
theorem checked62001 : checkPrefixCuts (2^48) 8130527233 10 Manual.Count131072.C062001.packed 64 cuts62001 = true := by
 decide +kernel
def pointBounds62001 : List (Nat × Nat × Nat) := [(8130641920,114321762694816,114322151333823)]
theorem point_links_checked62001 : (cuts62001.take 1).map (fun c => (8130527233-1+2*2^10*c.k,114321588179069+c.lower,114321976817977+c.upper)) = pointBounds62001 := by
 decide +kernel
def cuts62002 : List PrefixCut := [⟨64,196495609,196495726⟩]
theorem checked62002 : checkPrefixCuts (2^48) 8130658305 10 Manual.Count131072.C062002.packed 64 cuts62002 = true := by
 decide +kernel
def cuts62003 : List PrefixCut := [⟨53,162151486,162151583⟩,
⟨64,195730837,195730954⟩]
theorem checked62003 : checkPrefixCuts (2^48) 8130789377 10 Manual.Count131072.C062003.packed 64 cuts62003 = true := by
 decide +kernel
def pointBounds62003 : List (Nat × Nat × Nat) := [(8130897920,114322145194396,114322533833631)]
theorem point_links_checked62003 : (cuts62003.take 1).map (fun c => (8130789377-1+2*2^10*c.k,114321983042910+c.lower,114322371682048+c.upper)) = pointBounds62003 := by
 decide +kernel
def cuts62004 : List PrefixCut := [⟨64,198254762,198254882⟩]
theorem checked62004 : checkPrefixCuts (2^48) 8130920449 10 Manual.Count131072.C062004.packed 64 cuts62004 = true := by
 decide +kernel
def cuts62005 : List PrefixCut := [⟨50,154495953,154496042⟩,
⟨64,196866896,196867011⟩]
theorem checked62005 : checkPrefixCuts (2^48) 8131051521 10 Manual.Count131072.C062005.packed 64 cuts62005 = true := by
 decide +kernel
def pointBounds62005 : List (Nat × Nat × Nat) := [(8131153920,114322531524462,114322920163926)]
theorem point_links_checked62005 : (cuts62005.take 1).map (fun c => (8131051521-1+2*2^10*c.k,114322377028509+c.lower,114322765667884+c.upper)) = pointBounds62005 := by
 decide +kernel
def cuts62006 : List PrefixCut := [⟨64,201156149,201156268⟩]
theorem checked62006 : checkPrefixCuts (2^48) 8131182593 10 Manual.Count131072.C062006.packed 64 cuts62006 = true := by
 decide +kernel
def cuts62007 : List PrefixCut := [⟨47,146217810,146217896⟩,
⟨64,198037483,198037601⟩]
theorem checked62007 : checkPrefixCuts (2^48) 8131313665 10 Manual.Count131072.C062007.packed 64 cuts62007 = true := by
 decide +kernel
def pointBounds62007 : List (Nat × Nat × Nat) := [(8131409920,114322921269364,114323309909059)]
theorem point_links_checked62007 : (cuts62007.take 1).map (fun c => (8131313665-1+2*2^10*c.k,114322775051554+c.lower,114323163691163+c.upper)) = pointBounds62007 := by
 decide +kernel
def cuts62008 : List PrefixCut := [⟨64,199072759,199072870⟩]
theorem checked62008 : checkPrefixCuts (2^48) 8131444737 10 Manual.Count131072.C062008.packed 64 cuts62008 = true := by
 decide +kernel
def cuts62009 : List PrefixCut := [⟨44,134686406,134686485⟩,
⟨64,196196511,196196626⟩]
theorem checked62009 : checkPrefixCuts (2^48) 8131575809 10 Manual.Count131072.C062009.packed 64 cuts62009 = true := by
 decide +kernel
def pointBounds62009 : List (Nat × Nat × Nat) := [(8131665920,114323306848202,114323695488119)]
theorem point_links_checked62009 : (cuts62009.take 1).map (fun c => (8131575809-1+2*2^10*c.k,114323172161796+c.lower,114323560801634+c.upper)) = pointBounds62009 := by
 decide +kernel
def cuts62010 : List PrefixCut := [⟨64,197335612,197335726⟩]
theorem checked62010 : checkPrefixCuts (2^48) 8131706881 10 Manual.Count131072.C062010.packed 64 cuts62010 = true := by
 decide +kernel
def cuts62011 : List PrefixCut := [⟨41,129663127,129663197⟩,
⟨64,201659158,201659269⟩]
theorem checked62011 : checkPrefixCuts (2^48) 8131837953 10 Manual.Count131072.C062011.packed 64 cuts62011 = true := by
 decide +kernel
def pointBounds62011 : List (Nat × Nat × Nat) := [(8131921920,114323695357046,114324083997183)]
theorem point_links_checked62011 : (cuts62011.take 1).map (fun c => (8131837953-1+2*2^10*c.k,114323565693919+c.lower,114323954333986+c.upper)) = pointBounds62011 := by
 decide +kernel
def cuts62012 : List PrefixCut := [⟨64,197779235,197779351⟩]
theorem checked62012 : checkPrefixCuts (2^48) 8131969025 10 Manual.Count131072.C062012.packed 64 cuts62012 = true := by
 decide +kernel
def cuts62013 : List PrefixCut := [⟨38,117406117,117406187⟩,
⟨64,198883643,198883760⟩]
theorem checked62013 : checkPrefixCuts (2^48) 8132100097 10 Manual.Count131072.C062013.packed 64 cuts62013 = true := by
 decide +kernel
def pointBounds62013 : List (Nat × Nat × Nat) := [(8132177920,114324082538429,114324471178793)]
theorem point_links_checked62013 : (cuts62013.take 1).map (fun c => (8132100097-1+2*2^10*c.k,114323965132312+c.lower,114324353772606+c.upper)) = pointBounds62013 := by
 decide +kernel
def cuts62014 : List PrefixCut := [⟨64,198015123,198015240⟩]
theorem checked62014 : checkPrefixCuts (2^48) 8132231169 10 Manual.Count131072.C062014.packed 64 cuts62014 = true := by
 decide +kernel
def cuts62015 : List PrefixCut := [⟨35,108853324,108853389⟩,
⟨64,198150395,198150512⟩]
theorem checked62015 : checkPrefixCuts (2^48) 8132362241 10 Manual.Count131072.C062015.packed 64 cuts62015 = true := by
 decide +kernel
def pointBounds62015 : List (Nat × Nat × Nat) := [(8132433920,114324470884402,114324859524995)]
theorem point_links_checked62015 : (cuts62015.take 1).map (fun c => (8132362241-1+2*2^10*c.k,114324362031078+c.lower,114324750671606+c.upper)) = pointBounds62015 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000062
