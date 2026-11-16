import PlattPointSubsetKernel
import PlattPointPackets.S5B000047
import PlattPointPackets.S5B000048
import PlattPointPackets.S5B000049
import PlattPointPackets.S5B000050
import PlattPointPackets.S5B000051
import PlattPointPackets.S5B000052
import PlattPointPackets.S5B000053
import PlattPointPackets.S5B000054
import PlattPointPackets.S5B000055
import PlattPointPackets.S5B000056
import PlattPointPackets.S5B000057
import PlattGlobalGrid.S8B000041
namespace ChenEffective.PlattWindow.PointCovers.S8B000041
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S5B000047.points ++ ChenEffective.PlattWindow.PointPackets.S5B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000057.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000041.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000041.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000041
