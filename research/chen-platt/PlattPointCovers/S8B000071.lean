import PlattPointSubsetKernel
import PlattPointPackets.S6B000088
import PlattPointPackets.S6B000089
import PlattPointPackets.S6B000090
import PlattPointPackets.S6B000091
import PlattPointPackets.S6B000092
import PlattPointPackets.S6B000093
import PlattPointPackets.S6B000094
import PlattPointPackets.S6B000095
import PlattPointPackets.S6B000096
import PlattPointPackets.S6B000097
import PlattPointPackets.S6B000098
import PlattPointPackets.S6B000099
import PlattPointPackets.S6B000100
import PlattPointPackets.S6B000101
import PlattPointPackets.S6B000102
import PlattGlobalGrid.S8B000071
namespace ChenEffective.PlattWindow.PointCovers.S8B000071
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000088.points ++ ChenEffective.PlattWindow.PointPackets.S6B000089.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000102.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000071.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000071.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000071
