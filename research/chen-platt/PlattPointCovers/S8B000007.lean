import PlattPointSubsetKernel
import PlattPointPackets.S4B000048
import PlattPointPackets.S4B000049
import PlattPointPackets.S4B000050
import PlattPointPackets.S4B000051
import PlattPointPackets.S4B000052
import PlattPointPackets.S4B000053
import PlattPointPackets.S4B000054
import PlattPointPackets.S4B000055
import PlattPointPackets.S4B000056
import PlattGlobalGrid.S8B000007
namespace ChenEffective.PlattWindow.PointCovers.S8B000007
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000048.points ++ ChenEffective.PlattWindow.PointPackets.S4B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000056.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000007.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000007.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000007
