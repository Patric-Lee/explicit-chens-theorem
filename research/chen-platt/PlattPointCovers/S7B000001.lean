import PlattPointSubsetKernel
import PlattPointPackets.S2B000052
import PlattPointPackets.S2B000053
import PlattPointPackets.S2B000054
import PlattPointPackets.S2B000055
import PlattGlobalGrid.S7B000001
namespace ChenEffective.PlattWindow.PointCovers.S7B000001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000052.points ++ ChenEffective.PlattWindow.PointPackets.S2B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000055.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000001.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000001.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000001
