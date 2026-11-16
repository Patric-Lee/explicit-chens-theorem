import PlattPointSubsetKernel
import PlattPointPackets.S5B000006
import PlattPointPackets.S5B000007
import PlattPointPackets.S5B000008
import PlattPointPackets.S5B000009
import PlattPointPackets.S5B000010
import PlattPointPackets.S5B000011
import PlattPointPackets.S5B000012
import PlattPointPackets.S5B000013
import PlattPointPackets.S5B000014
import PlattPointPackets.S5B000015
import PlattPointPackets.S5B000016
import PlattGlobalGrid.S8B000037
namespace ChenEffective.PlattWindow.PointCovers.S8B000037
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S5B000006.points ++ ChenEffective.PlattWindow.PointPackets.S5B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000016.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000037.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000037.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000037
